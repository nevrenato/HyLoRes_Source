module HyLoRes.Core.Worker.Base

where

import HyLoRes.Formula           ( At, Opaque )
import HyLoRes.Clause.FullClause ( FullClause )
import HyLoRes.ModelGen          ( HerbrandModel )

data Result = SAT HerbrandModel | UNSAT | INTERRUPTED

data Directive = Abort
               | Exhausted
               | Continue [FullClause (At Opaque)]
               | AllSubsumed

type CycleCount = Int -- Used for picking the oldest clause as given

