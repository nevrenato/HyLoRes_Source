{-# OPTIONS_GHC -fno-warn-incomplete-patterns #-}
module HyLoRes.Core.Worker (
    Worker,
    Serial, runSerial,
    SMP,    runSMP,

    --

    onClauseSet, onClauseSet_, fromClauseSet, onClausesIndex_,

    cycleCount, incCycleCount,

    param, params,

    getDirective, unsatDetected, postProcessNew
)

where

import HyLoRes.Logger     ( MonadLogger(..) )
import HyLoRes.Statistics ( MonadStatistics(..) )
import HyLoRes.ClauseSet  ( ClauseSet )

import HyLoRes.Config             ( Params (..) )
import HyLoRes.Clause.SelFunction ( SelFunc )
import HyLoRes.Statistics         ( StatsValues )
import HyLoRes.Core.Worker.Base ( CycleCount, Directive )

import qualified HyLoRes.Core.Worker.Serial as Serial
import qualified HyLoRes.Core.SMP.Worker as SMP

import HyLoRes.Subsumption.CASSubsumptionTrie ( CASSubsumptionTrie )
import HyLoRes.Subsumption.ClausesByFormulaIndex

import Data.IORef


import HyLoRes.Util.Timeout ( TimeoutSignal )

import Control.Concurrent.MVar

data Serial
data SMP

data Witness t where
    Serial :: Witness Serial
    SMP    :: Witness SMP

data Implementation t a where
    I1 :: Serial.Worker a -> Implementation Serial a
    I2 ::    SMP.Worker a -> Implementation SMP    a

type Worker_ t a = Witness t -> Implementation t a

-- wrap a Worker_ in a newtype to make it an instance of Monad
newtype Worker t a = Wrap (Worker_ t a)

instance Monad (Worker t) where
    {-# INLINE return #-}
    return a = Wrap $ pick (return a) (return a)

    {-# INLINE fail #-}
    fail   s = Wrap $ pick (fail s) (fail s)

    {-# INLINE (>>=) #-}
    m >>= f  = Wrap $ bind m f

    {-# INLINE (>>) #-}
    m >> m'  = m >>= \_ -> m'

{-# INLINE bind #-}
bind :: forall a b t . Worker t a -> (a -> Worker t b) -> Worker_ t b
bind (Wrap worker) f = \w ->
    case w of
      Serial -> case worker Serial of
                  I1 m -> I1 (do a <- m
                                 case f a of
                                   Wrap worker' -> case worker' Serial of
                                                     I1 m' -> m'
                             :: Serial.Worker b)
      SMP    -> case worker SMP of
                  I2 m -> I2 (do a <- m
                                 case f a of
                                   Wrap worker' -> case worker' SMP of
                                                     I2 m' -> m'
                             :: SMP.Worker b)

{-# INLINE pick #-}
pick :: Serial.Worker a -> SMP.Worker a -> Worker_ t a
pick serial smp = \w -> case w of
                          Serial -> I1 serial
                          SMP    -> I2 smp

instance MonadLogger (Worker t) where
    mustLogEvent e = Wrap $ pick (mustLogEvent e) (mustLogEvent e)
    performLog   s = Wrap $ pick (performLog   s) (performLog   s)

instance MonadStatistics (Worker t) where
    getStatsValues = Wrap $ pick getStatsValues getStatsValues
    performIO a    = Wrap $ pick (performIO a)  (performIO a)

onClauseSet_ :: (ClauseSet -> ClauseSet)  -> Worker t ()
onClauseSet_ f = Wrap $ pick (Serial.onClauseSet_ f) (SMP.onClauseSet_ f)

onClauseSet :: (ClauseSet -> (ClauseSet, a))  -> Worker t a
onClauseSet f = Wrap $ pick (Serial.onClauseSet f) (SMP.onClauseSet f)

fromClauseSet :: (ClauseSet -> a)  -> Worker t a
fromClauseSet f = Wrap $ pick (Serial.fromClauseSet f) (SMP.fromClauseSet f)

onClausesIndex_ :: (ClausesByFormulaIndex -> ClausesByFormulaIndex) -> Worker t ()
onClausesIndex_ f = Wrap $ pick (Serial.onClausesIndex_ f)  (SMP.onClausesIndex_ f)

cycleCount :: Worker t CycleCount
cycleCount = Wrap $ pick Serial.cycleCount SMP.cycleCount

incCycleCount :: Worker t ()
incCycleCount = Wrap $ pick Serial.incCycleCount SMP.incCycleCount

params :: Worker t Params
params = Wrap $ pick Serial.params SMP.params

param :: (Params -> a) -> Worker t a
param f = Wrap $ pick (Serial.param f) (SMP.param f)

getDirective :: Worker t Directive
getDirective = Wrap $ pick Serial.getDirective SMP.getDirective

unsatDetected :: Worker t ()
unsatDetected = Wrap $ pick (return ()) SMP.unsatDetected

postProcessNew :: Worker t ()
postProcessNew = Wrap $ pick Serial.postProcessNew SMP.postProcessNew

runSerial :: Worker Serial a
          -> Params
          -> SelFunc
          -> StatsValues
          -> TimeoutSignal
          -> IO a
runSerial (Wrap worker) = case worker Serial of
                            I1 m -> Serial.runWorker m

runSMP  :: Worker SMP a
        -> SMP.WorkerChans
        -> SMP.WorkerId
        -> Params
        -> StatsValues
	-> IORef CASSubsumptionTrie
	-> MVar ClausesByFormulaIndex
        -> IO a
runSMP (Wrap worker) = case worker SMP of
                         I2 m -> SMP.runWorker m

