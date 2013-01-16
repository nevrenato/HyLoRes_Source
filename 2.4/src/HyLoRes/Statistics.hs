----------------------------------------------------
--                                                --
-- HyLoRes.Statistics:                            --
-- Functions that collect and print out           --
-- statistics                                     --
--                                                --
----------------------------------------------------

{-
Copyright (C) HyLoRes 2002-2007 - See AUTHORS file

This program is free software; you can redistribute it and/or
modify it under the terms of the GNU General Public License
as published by the Free Software Foundation; either version 2
of the License, or (at your option) any later version.

This program is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with this program; if not, write to the Free Software
Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA  02111-1307,
USA.
-}

module HyLoRes.Statistics(
    -- the original idea was not to export MonadStatistcs methods,
    -- but this is required to implement the Worker type....
    MonadStatistics(..), StatisticsT, runStatisticsT,

    StatsValues,

    recordGivenClause, recordQueuedClauses,
    recordFiredRule, recordSubsumedPremise,
    recordLateSubsumedClause,

    showAllMetrics, logInspectionMetrics,

    mkStatsValues,

    Metric, UniqueMetric,
    rawClausesGenerated, nonFwSubsumedClausesGenerated,
    premisesSubsumedByConsequents, ruleApplicationCount,
    averageGivenClauseSize, lateSubsumedClauses

) where

import Prelude hiding ( log )

import Control.Monad        ( guard, when, liftM, liftM2 )
import Control.Monad.Trans  ( MonadTrans(lift), MonadIO(liftIO) )
import Control.Monad.Reader ( ReaderT, runReaderT, ask )

import Control.Applicative ( (<*>), (<$>) )

import Data.List  ( intersperse, nub, (\\) )
import Data.Maybe ( mapMaybe )

import Data.Unique ( Unique, newUnique )

import Data.Array.IO ( IOUArray, Ix, MArray,
                       newArray, readArray, writeArray, getAssocs )
import Data.IORef    ( IORef, newIORef, readIORef, writeIORef )

import HyLoRes.Clause             ( Clause(..) )
import HyLoRes.Clause.BasicClause ( BasicClause )
import HyLoRes.Clause.FullClause  ( FullClause )

import HyLoRes.Core.Rule.Metadata ( RuleId )

import HyLoRes.Logger ( MonadLogger, log, LoggerEvent (..) )


-------------------------------------------
-- Statistics are collections of Metrics
-- which can be printed out (at regular intervals)
-------------------------------------------
data StatsValues = Stat{metrics           :: [Metric],
                        inspectionMetrics :: [Metric],
                        count             :: IORef Int,
                        step              :: Maybe Int}



class Monad m => MonadStatistics m where
    getStatsValues :: m StatsValues
    performIO      :: IO a -> m a

newtype StatisticsT m a = StatsT{unStatsT :: ReaderT StatsValues m a}
                          deriving (Functor, Monad, MonadTrans, MonadIO)

instance MonadIO m => MonadStatistics (StatisticsT m) where
    getStatsValues = StatsT ask
    performIO      = liftIO

instance (MonadStatistics m, MonadTrans t, Monad (t m))
      => MonadStatistics (t m) where
    getStatsValues = lift getStatsValues
    performIO      = lift . performIO


runStatisticsT :: MonadIO m => StatisticsT m a -> StatsValues -> m a
runStatisticsT m = (unStatsT m `runReaderT`)

needsToPrintOut :: StatsValues -> IO Bool
needsToPrintOut (Stat _ [] _      _)         = return False
needsToPrintOut (Stat _ _  _      Nothing)   = return False
needsToPrintOut (Stat _ _  itRef (Just toi)) = do iter <- readIORef itRef
                                                  return $ iter > 0 &&
                                                           iter `mod` toi == 0

noStats :: StatsValues -> Bool
noStats (Stat [] [] _ _) = True
noStats  _               = False

mkStatsValues :: [UniqueMetric] -> Maybe (Int, [UniqueMetric]) -> IO StatsValues
mkStatsValues ms iims =
    do countRef <- newIORef 0
       --
       -- we remove "duplicated" metrics (i.e. no ioref occurs twice);
       -- otherwise, aliasing would give us wrong results
       let ims' = nub $ maybe [] snd iims
       let ms'  = nub ms \\ ims'
       --
       let toi = fmap fst iims
       --
       return Stat{metrics           = map unUnique ms',
                   inspectionMetrics = map unUnique ims',
                   count             = countRef,
                   step              = guard (maybe False (> 0) toi) >> toi}


updateMetrics :: MonadStatistics m => (Metric -> IO ()) -> m ()
updateMetrics f  = do stat <- getStatsValues
                      performIO $
                        mapM_ f (metrics stat ++ inspectionMetrics stat)

updateStep :: MonadStatistics m => m ()
updateStep = performIO . updateStep' =<< getStatsValues
    where updateStep' (Stat _ [] _ _)       = return ()
          updateStep' (Stat _ _  _ Nothing) = return ()
          updateStep' (Stat _ _  r _)       = modifyIORef' r (1 +)

recordGivenClause :: MonadStatistics m => FullClause f -> m ()
recordGivenClause cl  = do updateMetrics (recordGivenClauseM cl)
                           updateStep

recordFiredRule :: MonadStatistics m => RuleId -> [BasicClause] -> m ()
recordFiredRule rule cls = updateMetrics (recordFiredRuleM rule cls)

recordSubsumedPremise :: MonadStatistics m => m ()
recordSubsumedPremise = updateMetrics recordSubsumedPremiseM

recordLateSubsumedClause :: MonadStatistics m => Int -> m ()
recordLateSubsumedClause n = updateMetrics (recordLateSubsumedClauseM n)

recordQueuedClauses :: MonadStatistics m => [FullClause f] -> m ()
recordQueuedClauses cls = updateMetrics (recordQueuedClausesM cls)

showAllMetrics :: StatsValues -> IO String
showAllMetrics stats = if noStats stats
                         then return []
                         else do sms <- showMetricList $ inspectionMetrics stats
                                                      ++ metrics stats
                                 return $ "(final statistics)\n" ++ sms

logInspectionMetrics :: (MonadStatistics m, MonadLogger m) => m ()
logInspectionMetrics =
    do s <- getStatsValues
       shouldPrint <- performIO $ needsToPrintOut s
       when shouldPrint $ do
           iter <- performIO $ readIORef (count s)
           log L_Metric $ concat ["(partial statistics: iteration",
                                  show iter, ")"]
           log L_Metric =<< (performIO $ showMetricList (inspectionMetrics s))


showMetricList :: [Metric] -> IO String
showMetricList [] = return []
showMetricList ms = do sms <- mapM showMetric ms
                       return . unlines . intersperse separator $ "begin" :
                                                                  sms    ++
                                                                  ["end"]
    where separator = "---------------------"

--------------------------------------------
-- Metrics
--------------------------------------------
data Metric = CG  (IORef Int)
                  -- Raw clauses generated
                  -- (sum of the clauses generated by each rule)
                  --
            | CG' (IORef Int)
                  -- Non fw-subsumed clauses generated
                  --
            | SP  (IORef Int)
                  -- Number of premises that were subsumed by their consequents
                  --
            | LS  (IORef Int)
                  -- Number of Clauses subsumed already processed
                  --
            | RC  (IOUArray RuleId Int)
                  -- Rule application count
                  --
            | GS  (IORef Int) (IORef Int)
                  -- Avg size of the given clause
--            deriving(Eq) -- this uses ioref equality (pointer equality)
                           -- but IOUArray lacks an Eq instance (grrrr).
                           -- until fixed, we use a Unique

data UniqueMetric = UM{unique :: Unique, unUnique :: Metric}

instance Eq UniqueMetric where
    a == b = unique a == unique b

showMetric :: Metric -> IO String
showMetric (CG  x) =
    do n <- readIORef x
       return $ concat ["Clauses generated (raw): ", show n]

showMetric (CG' x) =
    do n <- readIORef x
       return $ concat ["Clauses generated (non forward-subsumed): ", show n]

showMetric (SP  x) =
    do n <- readIORef x
       return $ concat ["Premises subsumed by their consequents: ", show n]

showMetric (LS  x) =
    do n <- readIORef x
       return $ concat ["Late Subsumed Clauses: ", show n]

showMetric (GS  s c) =
    do (a,b) <- (,) <$> (readIORef s) <*> (readIORef c)
       return $ concat ["Avg. given clause size: ", show (ratio a b)]

showMetric (RC  x) =
    do as <- getAssocs x
       let rs = "Rule applications:": mapMaybe showRule as
       return . concat . intersperse "\n" $ rs
    where  showRule (i,c) = do guard (c > 0)
                               return $ concat ["  ",show i, " rule: ", show c]

modifyIORef' :: IORef a -> (a -> a) -> IO ()
modifyIORef' r f = do new <- liftM f (readIORef r)
                      writeIORef r $! new

modifyArray :: (MArray a e m, Ix i) => a i e -> i -> (e -> e) -> m ()
modifyArray a i f = do new <- liftM f (readArray a i)
                       writeArray a i $! new

recordGivenClauseM :: FullClause f -> Metric -> IO ()
recordGivenClauseM cl (GS s c) = do modifyIORef' s (size cl +)
                                    modifyIORef' c (1 +)
recordGivenClauseM _   _       = return ()

recordQueuedClausesM :: [FullClause f] -> Metric -> IO ()
recordQueuedClausesM cls (CG' x) = modifyIORef' x (length cls +)
recordQueuedClausesM _   _       = return ()

recordFiredRuleM :: RuleId -> [BasicClause] -> Metric -> IO ()
recordFiredRuleM _    cls (CG x) = modifyIORef' x (length cls +)
recordFiredRuleM rule _   (RC a) = modifyArray a rule  (1 +)
recordFiredRuleM _    _    _     = return ()

recordSubsumedPremiseM :: Metric -> IO ()
recordSubsumedPremiseM (SP x) = modifyIORef' x (1+)
recordSubsumedPremiseM  _     = return ()

recordLateSubsumedClauseM :: Int -> Metric -> IO ()
recordLateSubsumedClauseM n (LS x) = modifyIORef' x (n+)
recordLateSubsumedClauseM  _ _     = return ()

ratio :: Int -> Int -> Float
ratio x y = (fromIntegral x) / (fromIntegral y)

------------------------------------ Metric builders -------------

mkUnique :: IO Metric -> IO UniqueMetric
mkUnique = liftM2 UM newUnique

rawClausesGenerated :: IO UniqueMetric
rawClausesGenerated = mkUnique . liftM CG $ newIORef 0

nonFwSubsumedClausesGenerated :: IO UniqueMetric
nonFwSubsumedClausesGenerated = mkUnique . liftM CG' $ newIORef 0

premisesSubsumedByConsequents :: IO UniqueMetric
premisesSubsumedByConsequents = mkUnique . liftM SP $ newIORef 0

lateSubsumedClauses :: IO UniqueMetric
lateSubsumedClauses = mkUnique . liftM LS $ newIORef 0

ruleApplicationCount :: IO UniqueMetric
ruleApplicationCount = mkUnique . liftM RC $ newArray (minBound, maxBound) 0

averageGivenClauseSize :: IO UniqueMetric
averageGivenClauseSize = mkUnique $ GS <$> (newIORef 0) <*> (newIORef 0)
