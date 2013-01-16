module HyLoRes.Core.SMP.Base (
    WorkerId, workerIdToInt,
    --
    ChWorkerToMain,
    ChDispatcherToMain,
    --
    ChWorkerToDispatcher,   MsgWorkerToDispatcher(..),
    ChDispatcherToWorker,   MsgDispatcherToWorker(..)
    --
)

where

import Control.Concurrent.Chan ( Chan )

import HyLoRes.Formula ( At, Opaque )

import Data.Array ( Ix )

import HyLoRes.Clause.BasicClause  ( BasicClause )
import HyLoRes.Clause.FullClause  ( FullClause )

import HyLoRes.Core.Worker.Base ( Result )

newtype WorkerId = W Int deriving (Read, Show, Eq, Ord, Enum, Ix, Num, Real, Integral)

type ChWorkerToMain         = Chan Result
type ChDispatcherToMain     = Chan Result

type ChWorkerToDispatcher   = Chan MsgWorkerToDispatcher
type ChDispatcherToWorker   = Chan MsgDispatcherToWorker


data MsgDispatcherToWorker   = GET_INUSE
                             | D2W_CLAUSES [FullClause (At Opaque)]

data MsgWorkerToDispatcher   = NEW Int [BasicClause]
                             | INUSE [FullClause (At Opaque)]
workerIdToInt :: WorkerId -> Int
workerIdToInt (W i) = i
