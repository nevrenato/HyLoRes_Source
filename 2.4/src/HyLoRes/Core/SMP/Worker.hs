module HyLoRes.Core.SMP.Worker(
    Worker, WorkerId, workerIdToInt,

    WorkerChans(..),

    runWorker,

    param, params, channels, channel, workerId,

    cycleCount, incCycleCount,

    onClauseSet, onClauseSet_, fromClauseSet, onClausesIndex_,

    getDirective, unsatDetected, postProcessNew
)

where

import Prelude hiding ( log, cycle )

import Control.Applicative ( (<$>) )


import Data.List            ( sortBy , foldl')
import Data.Maybe

import Control.Concurrent.Chan
import Control.Monad.State
import Control.Monad.Reader
import Control.Concurrent.MVar

import qualified Data.Set as Set
import qualified Data.EnumSet as ESet

import HyLoRes.Clause.BasicClause ( BasicClause )
import HyLoRes.Clause.FullClause  ( FullClause, specialize, ClauseId )
import HyLoRes.Clause             ( size )
import HyLoRes.Formula.TypeLevel  ( Spec(..) )

import HyLoRes.ClauseSet.InUse (InUseClauseSet, allClauses)
import HyLoRes.Formula         ( At, Opaque )

import HyLoRes.ClauseSet ( ClauseSet )
import qualified HyLoRes.ClauseSet as CS

import HyLoRes.Subsumption.CASSubsumptionTrie ( CASSubsumptionTrie )
import qualified HyLoRes.Subsumption.CASSubsumptionTrie as ST

import HyLoRes.Subsumption.ClausesByFormulaIndex ( ClausesByFormulaIndex )
import qualified HyLoRes.Subsumption.ClausesByFormulaIndex as CbFI

import Data.IORef

import HyLoRes.Core.Worker.Base ( Result(..), CycleCount, Directive(..) )

import HyLoRes.Core.SMP.Base ( WorkerId, workerIdToInt,
                               ChWorkerToMain,
                               ChWorkerToDispatcher, MsgWorkerToDispatcher(..),
                               ChDispatcherToWorker, MsgDispatcherToWorker(..) )

import HyLoRes.Config ( Params (..) )
import HyLoRes.Logger ( MonadLogger, LoggerT, runLoggerT, log, LoggerEvent(..) )

import HyLoRes.Statistics ( StatisticsT, runStatisticsT,
                            MonadStatistics, StatsValues )

import HyLoRes.FrontEnd.PrettyPrint ( logSubsumptions, logBwSubsumptions )

import HyLoRes.Util         ( compareUsing )

data WorkerChans = WC {toMain         :: ChWorkerToMain,
                       fromDispatcher :: ChDispatcherToWorker,
                       toDispatcher   :: ChWorkerToDispatcher}

newtype Worker a = WR {unWR :: ReaderT Params      (
                               ReaderT WorkerChans (
                               ReaderT WorkerId    (
                               LoggerT             (
                               StatisticsT         (
                               StateT WorkerState  (
                               StateT (IORef CASSubsumptionTrie)(
                               ReaderT (MVar ClausesByFormulaIndex)
                               IO))))))) a}
                         deriving (Functor, Monad, MonadIO,
                                   MonadStatistics, MonadLogger)

data WorkerState = S{
                     cycle       :: CycleCount,
                     clauseSet   :: ClauseSet,
                     clausesSize :: Int, -- Used to calculate the number of
                                         -- clauses removed from
                                         -- from Clauses on each cycle (because
                                         -- of ParUnit, this can be arbitrarly
                                         -- large)
                     clsIds      :: Set.Set ClauseId
                     } -- Used to store clauses Ids received
                       -- from dispatcher to avoid duplicates

readFromDispatcher :: Bool -> Worker MsgDispatcherToWorker
readFromDispatcher ok_to_block =
    do chans     <- channels
       emptyChan <- liftIO $ isEmptyChan (fromDispatcher chans)
       if (ok_to_block || not emptyChan)
           then liftIO $ readChan (fromDispatcher chans)
           else return $ D2W_CLAUSES []

sendToDispatcher :: Int -> [BasicClause] -> Worker ()
sendToDispatcher processed new =
    do chans <- channels
       liftIO $ writeChan (toDispatcher chans) (NEW processed new)

sendInUseToDispatcher :: InUseClauseSet -> Worker ()
sendInUseToDispatcher inUse =
    do chans <- channels
       liftIO $ writeChan (toDispatcher chans) (INUSE (allClauses inUse))

sendToMain :: Result -> Worker ()
sendToMain result = do chans <- channels
                       liftIO $ writeChan (toMain chans) result

isEq :: FullClause (At Opaque) -> Bool
isEq cl = case specialize cl of
              AtNom c -> size c == 1
              _       -> False

isRelDiam :: FullClause (At Opaque) -> Bool
isRelDiam cl = case specialize cl of
                 AtDiamNom{} -> True
                 _           -> False

subsumptionCheck :: FullClause (At Opaque) -> Worker Bool
subsumptionCheck fcl =
    do tr <- trie
       subsumed <- liftIO $ subsumes fcl tr
       if subsumed
         then return False
         else do checkBW <- param bwSubsIsOn
                 when checkBW $ do
                    mvar <- cbIndex
                    cbf <- liftIO $ takeMVar mvar
                    let (bwSubs,cbf') = CbFI.addToIndexLookupSubs fcl cbf
                    let bws = ESet.toList bwSubs
                    --
                    removedCls <- mapM (onClauseSet . CS.removeClauseById) bws
                    logBwSubsumptions fcl bws
                    let cbf'' = foldl' (flip CbFI.removeFromIndex)
                                       cbf'
                                       (catMaybes removedCls)
                    liftIO $ putMVar mvar cbf''
                 return True

subsumes :: FullClause (At Opaque) -> IORef CASSubsumptionTrie->  IO (Bool)
subsumes cl tr = -- If the clause is Eq or a Rel Diam add it to trie
                 -- and always return False since those clauses are sent to
                 -- more than one Worker and all of them should process it
                 do if isEq cl || isRelDiam cl
                     then do ST.add cl tr
                             return False
                     else do subsumed <- ST.subsumes tr cl
                             if subsumed
                               then return True
                               else do ST.add cl tr
                                       return False

runWorker :: Worker a
          -> WorkerChans
          -> WorkerId
          -> Params
          -> StatsValues
          -> IORef CASSubsumptionTrie
          -> MVar ClausesByFormulaIndex
          -> IO a
runWorker w wc wId p s st cbi = (`runReaderT` cbi)
                                . (`evalStateT` st)
                                . (`evalStateT` initialState)
                                . (`runStatisticsT` s)
                                . (`runLoggerT` (logPref, loggerCfg p))
                                . (`runReaderT` wId)
                                . (`runReaderT` wc)
                                . (`runReaderT` p)
                                . unWR $ w
    where initialState = S{cycle       = 0,
                           clauseSet   = CS.empty (clausesOrd p),
                           clausesSize = 0,
                           clsIds      = Set.empty}
          logPref        = concat ["[", show wId, "]: "]


onClauseSet_ :: (ClauseSet -> ClauseSet) -> Worker ()
onClauseSet_ f = WR (lift . lift . lift . lift . lift $ m)
    where m = modify $ \s -> s{clauseSet = f (clauseSet s)}

onClauseSet :: (ClauseSet -> (ClauseSet, a)) -> Worker a
onClauseSet f = WR (lift . lift . lift . lift . lift $ m)
    where m = do s <- get
                 let (cs',r) = f (clauseSet s)
                 put s{clauseSet = cs'}
                 return r

onClausesIndex_ :: (ClausesByFormulaIndex -> ClausesByFormulaIndex) -> Worker ()
onClausesIndex_ f =  do mvar <- cbIndex
                        cbf <- liftIO $ takeMVar mvar
                        liftIO $ putMVar mvar (f cbf)

fromClauseSet :: (ClauseSet -> a) -> Worker a
fromClauseSet f = WR (lift . lift . lift . lift . lift $ gets (f . clauseSet))

cycleCount :: Worker CycleCount
cycleCount = WR  (lift . lift . lift . lift . lift  $ gets cycle)

trie :: Worker (IORef CASSubsumptionTrie)
trie = WR  (lift . lift . lift .lift . lift . lift  $ get)

cbIndex :: Worker (MVar ClausesByFormulaIndex)
cbIndex = WR (lift . lift . lift . lift . lift . lift . lift $ ask)

incCycleCount :: Worker ()
incCycleCount = WR (lift . lift . lift . lift . lift  $ modify addOne)
    where addOne s = s{cycle = 1 + cycle s}

savedClausesSize :: Worker Int
savedClausesSize = WR (lift . lift . lift . lift . lift $ gets clausesSize)

resetSavedClausesSize :: Int -> Worker ()
resetSavedClausesSize n = WR (lift . lift . lift . lift . lift $ m)
    where m = modify $ \s -> s{clausesSize = n + CS.clausesSize (clauseSet s)}

--clausesIds :: Worker (Set.Set ClauseId)
--clausesIds = WR (lift . lift . lift . lift . lift  $ gets clsIds )

--addClauseId :: ClauseId -> Worker ()
--addClauseId clId = WR (lift . lift . lift . lift . lift $ m)
--    where m = modify $ \s -> s{clsIds = Set.insert clId (clsIds s)}

params :: Worker Params
params = WR ask

param :: (Params -> a) -> Worker a
param f = f <$> params

getDirective :: Worker Directive
getDirective = do ok_to_block   <- fromClauseSet CS.nothingInClauses
                  msg_from_disp <- readFromDispatcher ok_to_block
                  case msg_from_disp of
                    GET_INUSE ->
                        do in_use <- fromClauseSet CS.inUse
                           sendInUseToDispatcher in_use
                           return Abort
                    --
                    D2W_CLAUSES new_clauses ->
                        do  -- sort by size so potential subsumers are added first
                            let sorted_new = sortBy (compareUsing size) new_clauses

                            -- we reset the saved clauses size, taking into
                            -- into account the number of new clauses. this
                            -- value is later used during postprocessing to
                            -- infer the number of clauses actually processed
                            resetSavedClausesSize (length new_clauses)

                            (survived, subsumed) <- partitionM subsumptionCheck sorted_new

                            logSubsumptions subsumed
                            clauses_is_empty <- fromClauseSet CS.nothingInClauses


                            if clauses_is_empty && null survived
                               then return $ AllSubsumed
                               else return $ Continue survived

unsatDetected :: Worker ()
unsatDetected = sendToMain UNSAT

postProcessNew :: Worker ()
postProcessNew =
    do new <- fromClauseSet CS.new
       log L_Comm $ concat ["New : ", show new]
       --

       --
       clauses_size_on_start <- savedClausesSize
       current_clauses_size  <- fromClauseSet CS.clausesSize
       let processed_clauses = clauses_size_on_start - current_clauses_size
       --
       log L_Comm $ concat ["Processed clauses : ", show $ processed_clauses]
       sendToDispatcher processed_clauses new
       --
       onClauseSet_ CS.emptyNew

channels :: Worker WorkerChans
channels = WR (lift ask)

channel :: (WorkerChans -> a) -> Worker a
channel f = f <$> channels

workerId :: Worker WorkerId
workerId = WR (lift . lift $ ask)

partitionM :: Monad m => (a -> m Bool) -> [a] -> m ([a],[a])
partitionM p xs = sequence (map p' xs) >>= return . partitionEithers
    where p' a = do r <- p a; return $ if r then Left a else Right a

partitionEithers :: [Either a b] -> ([a],[b])
partitionEithers = foldr (either left right) ([],[])
    where left  a (l, r) = (a:l, r)
          right a (l, r) = (l, a:r)
