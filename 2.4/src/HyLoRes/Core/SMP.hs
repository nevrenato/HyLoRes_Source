module HyLoRes.Core.SMP ( runHyLoRes )

where

import Control.Concurrent

import Control.Monad.State

import Data.Array
import Data.IORef
import Data.Foldable ( foldMap )

import HyLoRes.Clause.BasicClause ( BasicClause )
import HyLoRes.Clause.SelFunction ( SelFunc, fromSelFuncString )

import qualified HyLoRes.Subsumption.CASSubsumptionTrie as ST
import qualified HyLoRes.Subsumption.ClausesByFormulaIndex as CBF

import HyLo.Signature ( getSignature )

import HyLoRes.Statistics ( StatsValues )

import HyLoRes.Core.Worker.Base ( Result(..) )

import HyLoRes.Core.SMP.Base       ( ChWorkerToMain )
import HyLoRes.Core.SMP.Worker     ( WorkerChans(..) )
import HyLoRes.Core.SMP.Dispatcher ( DispatcherChans (..), runDispatcher, DispatchAlgorithm (..), fromDispatchAlgString )

import qualified HyLoRes.Core.SMP.Worker   as WK

import HyLoRes.Core.Worker ( runSMP )

import HyLoRes.Core.GivenClauseAlg ( solve )

import HyLoRes.Config               ( Params(..))
import HyLoRes.FrontEnd.CommandLine ( CmdLineParams(..), configureStats )

import HyLoRes.Util.Timeout ( TimeoutSignal )



runHyLoRes :: Int    -- number of workers
           -> [BasicClause]
           -> Params
           -> CmdLineParams
           -> TimeoutSignal
           -> IO (Result, [StatsValues])
runHyLoRes num_workers input_clauses params clp timeout_signal =
    do (wIds, dId, c) <- connectParts num_workers
                                      (fromDispatchAlgString $ dispatchAlg clp)
                                      (fromSelFuncString $ selFuncStr clp)
                                      input_clauses
                                      params
                                      (configureStats clp)
                                      timeout_signal
       --
       result <- readChan c
       --
       let all_thread_ids = dId: map fst wIds
       forM all_thread_ids $ \threadId ->
            killThread threadId
        --
       return (result, map snd wIds);

connectParts :: Int
             -> DispatchAlgorithm
             -> SelFunc
             -> [BasicClause]
             -> Params
             -> IO StatsValues
             -> TimeoutSignal
             -> IO ([(ThreadId,StatsValues)],ThreadId,ChWorkerToMain)
connectParts n alg sf input_clauses p build_stats timeout_signal =
    do chanToMain <- newChan
       --
       let maxWId = fromIntegral (n - 1)
       --
       d2w <- listArray (0, maxWId) `liftM` sequence [newChan | _ <- [1 .. n]]
       w2d <- newChan
       trie <- newIORef ST.empty
       mvar <- newMVar CBF.emptyIndex
       --
       wIds <- forM (indices d2w) $ \i -> do
          stats <- build_stats
          --
          let chans = WC {toMain            = chanToMain,
                          WK.fromDispatcher = d2w ! i,
                          WK.toDispatcher   = w2d}
          --
          let input_sig = foldMap getSignature input_clauses
          let worker_action = solve input_sig >> return ()
          threadId <- forkIO $ runSMP worker_action chans i p stats trie mvar
          return (threadId, stats)
       --
       let dc = DC{dtoMain           = chanToMain,
                   toWorkers         = d2w,
                   fromWorkers       = w2d}


       dId  <- forkIO $ runDispatcher dc (loggerCfg p) sf input_clauses timeout_signal alg
       --
       return (wIds, dId, chanToMain)


