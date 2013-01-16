module HyLoRes.Core.SMP.Subsumer ( Channels(..), runSubsumer )

where

import Prelude hiding ( log )

import Control.Concurrent
import Control.Monad.State
import Control.Monad.Reader
import Control.Concurrent.Chan

import HyLoRes.Logger ( LoggerT, runLoggerT, LoggerCfg(..),
                        log, LoggerEvent(..) )

import HyLoRes.Subsumption.STMSubsumptionTrie ( STMSubsumptionTrie )
import qualified HyLoRes.Subsumption.STMSubsumptionTrie as ST

import HyLoRes.Core.SMP.Base ( ChSubsumerToDispatcher, ChDispatcherToSubsumer,
                               MsgDispatcherToSubsumer(..) )

import HyLoRes.Clause.FullClause ( FullClause )
import HyLoRes.Formula           ( At, Nom, Opaque )
import Control.Concurrent.STM


type ChChildToSubsumer = Chan SubsumptionResult

data SubsumptionResult = SUBSUMED
                       | CLAUSE (FullClause (At Nom Opaque))

data Channels = CH{fromDispatcher :: ChDispatcherToSubsumer,
                   toDispatcher   :: ChSubsumerToDispatcher}


data SData = SD{ checked  :: [FullClause (At Nom Opaque)] }

type Subsumer = ReaderT Channels       (
                LoggerT                (
                StateT (TVar STMSubsumptionTrie) (
                StateT SData
                IO)))


emptySD :: SData
emptySD = SD{checked = []}

runSubsumer :: Channels -> LoggerCfg -> TVar STMSubsumptionTrie -> IO ()
runSubsumer chs lc tr =  (`evalStateT` emptySD)
                         . (`evalStateT` tr)
                         . (`runLoggerT` ("[S]: ", lc))
                         . (`runReaderT` chs) $ subsumerLoop

runSubsumerChild :: ChChildToSubsumer
                 -> TVar STMSubsumptionTrie
                 -> FullClause (At Nom Opaque)
                 -> IO ()
runSubsumerChild fs tr cl = do result <- atomically (do subsumes cl tr)
                               writeChan fs result


subsumes :: FullClause (At Nom Opaque) -> TVar STMSubsumptionTrie->  STM (SubsumptionResult)
subsumes cl tr = do subsumed <- ST.subsumes tr cl
                    if subsumed
                     then return $ SUBSUMED
                     else do ST.add cl tr
                             return $ CLAUSE cl

subsumerLoop :: Subsumer ()
subsumerLoop =
  do chans <- channels
     m <- liftIO $ readChan (fromDispatcher chans)
     case m of
       STOP            -> return ()
       D2S_CLAUSES cls ->
         do let toCheck = length cls
            log L_Comm $ concat ["Clauses from Dispatcher: ", show toCheck]
            tr <- trie
        --    let notSubsumed = mapM checkLocalSubsumption cls tr
            --
            fc <- liftIO $ newChan

            forM_ cls $ \cl ->
              liftIO $ (forkIO $ runSubsumerChild fc tr cl)
            forM_ cls $ \_ -> do
               msg <- liftIO $ readChan fc
               case msg of
                 CLAUSE cl' -> addToChecked cl'
                 _          -> return ()

            --
            sd' <- sdata
            let subsumed = toCheck - (length $ checked sd')
            liftIO $ writeChan (toDispatcher chans)  (checked sd')
            log L_Comm $ concat ["Checked : ", show (checked sd')]
            log L_Comm $ concat ["Subsumed : ", show subsumed]
            lift . lift . lift $ put sd'{checked=[]}
            subsumerLoop


addToChecked :: FullClause (At Nom Opaque) -> Subsumer ()
addToChecked cl = do sd <- sdata
                     lift . lift . lift $ put sd{checked = cl : (checked sd)}

channels :: Subsumer Channels
channels = ask

trie :: Subsumer (TVar STMSubsumptionTrie)
trie = lift . lift $ get

sdata :: Subsumer SData
sdata = lift . lift . lift $ get
