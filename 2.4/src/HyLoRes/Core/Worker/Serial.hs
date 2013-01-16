module HyLoRes.Core.Worker.Serial (
    Worker, runWorker,

    onClauseSet, onClauseSet_, fromClauseSet, onClausesIndex_,
    cycleCount, incCycleCount,

    param, params,

    getDirective, postProcessNew
)

where

import Prelude hiding ( cycle )

import Data.List            ( sortBy, foldl' )

import qualified Data.EnumSet as Set

import Control.Monad        ( when )
import Control.Monad.Trans  ( MonadIO, lift )
import Control.Monad.Reader ( MonadReader(..), ReaderT, runReaderT, asks )
import Control.Monad.State  ( MonadState(..), StateT, evalStateT, gets, modify )

import HyLoRes.Statistics   ( StatisticsT, runStatisticsT,
                              MonadStatistics, StatsValues )
import HyLoRes.Logger ( MonadLogger, LoggerT, runLoggerT )

import HyLoRes.ClauseSet    ( ClauseSet, ClauseId )
import qualified HyLoRes.ClauseSet as CS

import HyLoRes.Subsumption.SubsumptionTrie ( SubsumptionTrie )
import qualified HyLoRes.Subsumption.SubsumptionTrie as ST

import HyLoRes.Subsumption.ClausesByFormulaIndex ( ClausesByFormulaIndex )
import qualified HyLoRes.Subsumption.ClausesByFormulaIndex as CbFI

import HyLoRes.Clause             ( Clause(size) )
import HyLoRes.Clause.BasicClause ( BasicClause, mergeAllDiamonds )
import HyLoRes.Clause.FullClause  ( FullClause, makeFullClause )
import HyLoRes.Clause.SelFunction ( SelFunc )

import HyLoRes.Formula     ( At, Opaque )

import HyLoRes.FrontEnd.PrettyPrint ( logSubsumptions, logBwSubsumptions )

import HyLoRes.Core.Worker.Base ( CycleCount, Directive(..) )

import HyLoRes.Config ( Params (..) )

import HyLoRes.Util         ( compareUsing )
import HyLoRes.Util.Timeout ( TimeoutSignal, isTimeout )

import Data.Maybe

newtype Worker a = W{unHLR :: ReaderT WorkerEnv   (
                              LoggerT             (
                              StatisticsT         (
                              StateT  WorkerState (
                              IO)))) a}
                    deriving (Functor, Monad, MonadIO,
                              MonadStatistics, MonadLogger)

instance MonadState WorkerState Worker where
    get   = W (lift . lift . lift $ get)
    put s = W (lift . lift . lift $ put s)

instance MonadReader WorkerEnv Worker where
    ask   = W ask
    local r (W m) = W (local r m)

data WorkerState = S{cycle     :: CycleCount,
                     nextClId  :: ClauseId,
                     clauseSet :: ClauseSet,
                     subsTrie  :: SubsumptionTrie,
                     cbfIdx    :: ClausesByFormulaIndex}

data WorkerEnv = E{parameters     :: Params,
                   selFunc        :: SelFunc,
                   timeout_signal :: TimeoutSignal}

runWorker::Worker a -> Params -> SelFunc -> StatsValues -> TimeoutSignal -> IO a
runWorker w p sf s ts = (`evalStateT` initialState)
                      . (`runStatisticsT` s)
                      . (`runLoggerT` ("", loggerCfg p))
                      . (`runReaderT` initialEnv)
                      . unHLR $ w
    where initialState = S{cycle     = 0,
                           nextClId  = 0,
                           clauseSet = CS.empty (clausesOrd p),
                           subsTrie  = ST.empty,
                           cbfIdx    = CbFI.emptyIndex}
          --
          initialEnv = E{parameters     = p,
                         selFunc        = sf,
                         timeout_signal = ts}

onClauseSet_ :: (ClauseSet -> ClauseSet) -> Worker ()
onClauseSet_ f =  modify $ \s -> s{clauseSet = f (clauseSet s)}

onClauseSet :: (ClauseSet -> (ClauseSet, a)) -> Worker a
onClauseSet f = do s <- get
                   let (cs',r) = f (clauseSet s)
                   put s{clauseSet = cs'}
                   return r

onClausesIndex_ :: (ClausesByFormulaIndex -> ClausesByFormulaIndex) -> Worker ()
onClausesIndex_ f =  modify $ \s -> s{cbfIdx = f (cbfIdx s)}

fromClauseSet :: (ClauseSet -> a) -> Worker a
fromClauseSet f = gets (f . clauseSet)

cycleCount :: Worker CycleCount
cycleCount = gets cycle

incCycleCount :: Worker ()
incCycleCount = modify (\s -> s{cycle = cycle s + 1})

params :: Worker Params
params = asks parameters

param :: (Params -> a) -> Worker a
param f = asks (f . parameters)

getDirective :: Worker Directive
getDirective =
    do timeout <- isTimeout =<< asks timeout_signal
       if timeout
         then return Abort
         else do new <- fromClauseSet CS.new
                 --
                 clauses_is_empty <- fromClauseSet CS.nothingInClauses
                 onClauseSet_ CS.emptyNew
                 --
                 -- sort by size so potential subsumers are added first
                 let sorted_new = sortBy (compareUsing size) new
                 full_cls <- mapM toFullClause sorted_new
                 (survived, subsumed) <- partitionM subsumptionCheck full_cls
                 logSubsumptions subsumed
                 return $ if clauses_is_empty && null survived
                          then Exhausted
                          else Continue survived

partitionM :: Monad m => (a -> m Bool) -> [a] -> m ([a],[a])
partitionM p xs = sequence (map p' xs) >>= return . partitionEithers
    where p' a = do r <- p a; return $ if r then Left a else Right a

partitionEithers :: [Either a b] -> ([a],[b])
partitionEithers = foldr (either left right) ([],[])
    where left  a (l, r) = (a:l, r)
          right a (l, r) = (l, a:r)

toFullClause :: BasicClause -> Worker (FullClause (At Opaque))
toFullClause cl = do s  <- get
                     sf <- asks selFunc
                     put s{nextClId = 1 + nextClId s}
                     return $ makeFullClause sf (nextClId s) cl


subsumptionCheck :: FullClause (At Opaque) -> Worker Bool
subsumptionCheck cl =
    do trie <- gets subsTrie
       if ST.subsumes trie cl
         then return False
         else do modify $ \s -> s{subsTrie = ST.add cl (subsTrie s)}
                 --
                 checkBW <- param bwSubsIsOn
                 when checkBW $ do
                    cbf <- gets cbfIdx
                    let (bwSubs,cbf') = CbFI.addToIndexLookupSubs cl cbf
                    let bws = Set.toList bwSubs
                    --
                    removedCls <- mapM (onClauseSet . CS.removeClauseById) bws
                    logBwSubsumptions cl bws
                    let cbf'' = foldl' (flip CbFI.removeFromIndex)
                                       cbf'
                                       (catMaybes removedCls)
                    --
                    modify $ \s -> s{cbfIdx = cbf''}
                 --
                 return True


postProcessNew :: Worker ()
postProcessNew = do new' <- map mergeAllDiamonds `fmap` fromClauseSet CS.new
                    onClauseSet_ (CS.addAllToNew new' . CS.emptyNew)
