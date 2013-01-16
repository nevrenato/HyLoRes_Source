----------------------------------------------------
--                                                --
-- HyLoRes.ClauseSet:                             --
-- Keeps all the clauses (New, Clauses, InUse)    --
-- used in the calculus. Answers subsumption      --
-- queries.                                       --
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

module HyLoRes.ClauseSet(
    -- types
    ClauseSet, ClauseId,

    -- new
    emptyNew, addToNew, addAllToNew,
    new, sizeOfNew, newContainsEmptyClause,

    -- clauses
    addAllToClauses,
    minInClauses, oldestInClauses, nothingInClauses, clausesSize,

    -- in-use
    addToInUse, removeFromInUse, inUse,

    -- as a whole
    empty, removeClauseById, getAllFullClauses, containsClause
)

where

import Data.List ( foldl' )
import Data.Foldable (any)
import qualified Data.Foldable as Foldable
import Data.EnumMap ( EnumMap, (!) )
import qualified Data.EnumMap as EMap

import HyLoRes.Formula ( At, Opaque )

import HyLoRes.Clause             ( Clause(..) )
import HyLoRes.Clause.BasicClause ( BasicClause )
import HyLoRes.Clause.FullClause  ( FullClause, ClauseId,
                                    clauseId, opaqueClause )

import HyLoRes.ClauseSet.Clauses ( ClausesClauseSet, ComplexityParamStr )
import qualified HyLoRes.ClauseSet.Clauses as CCS

import           HyLoRes.ClauseSet.InUse ( InUseClauseSet )
import qualified HyLoRes.ClauseSet.InUse as IU



type New     = [BasicClause]
type Clauses = ClausesClauseSet
type InUse   = InUseClauseSet

data ClauseLocation = Clauses | InUse | None

data ClauseSet = CS{
    new            :: New,
    clauses        :: Clauses,
    inUse          :: InUse,
    allFullClauses :: EnumMap ClauseId (ClauseLocation, FullClause (At Opaque))
    }


{- empty: Given

  - a complexity param string pan

  returns a new, empty, clause repository, with
  p as the complexity filter of the Clauses set.
-}
empty :: ComplexityParamStr -> ClauseSet
empty p = CS{new              = [],
             clauses          = CCS.newSet p,
             inUse            = IU.newSet,
             allFullClauses   = EMap.empty}


getAllFullClauses :: ClauseSet -> [FullClause (At Opaque)]
getAllFullClauses = map snd . EMap.elems . allFullClauses

-------------------------------------------------------------------------------
-- New clauses set                                                           --
-------------------------------------------------------------------------------

{- addToNew: Given

  - a BasicClause cl
  - a ClauseSet cs

  merges all diamonds in cl and adds the result to cs.New
-}
addToNew :: BasicClause -> ClauseSet -> ClauseSet
addToNew cl cs = cs{new = cl:new cs}

{- addAllToNew: Given

  - a list of BasicClauses
  - a ClauseSet cs

  adds all the given clauses to New (using addToNew)
-}
addAllToNew :: [BasicClause] -> ClauseSet -> ClauseSet
addAllToNew cls cs = cs{new = cls ++ new cs}



{- newContainsEmptyClause:
  returns True iff the New clauses set contains the empty clause
-}
newContainsEmptyClause :: ClauseSet -> Bool
newContainsEmptyClause = Foldable.any isEmpty . new

{- sizeOfNew:
  returns the number of clauses in New
-}
sizeOfNew :: ClauseSet -> Int
sizeOfNew = length . new

emptyNew :: ClauseSet -> ClauseSet
emptyNew cs = cs {new =[]}

-------------------------------------------------------------------------------
-- Clauses set                                                               --
-------------------------------------------------------------------------------

addAllToClauses :: [FullClause (At Opaque)] -> ClauseSet -> ClauseSet
addAllToClauses cls cs = foldl' addToClauses cs cls

addToClauses :: ClauseSet -> FullClause (At Opaque) -> ClauseSet
addToClauses cs cl = cs{clauses        = CCS.add cl (clauses cs),
                        allFullClauses = EMap.insert (clauseId cl)
                                                     (Clauses, cl)
                                                     (allFullClauses cs)}

removeFromClauses :: FullClause (At Opaque) -> ClauseSet -> ClauseSet
removeFromClauses cl cs = removeFromIndexes cl cs'
    where cs' = cs{clauses = CCS.removeById (clauseId cl) (clauses cs)}

containsClause :: ClauseSet -> FullClause (At Opaque) -> Bool
containsClause cs cl = CCS.containsClause (clauseId cl) (clauses cs)

removeFromIndexes :: FullClause f ->  ClauseSet -> ClauseSet
removeFromIndexes cl cs = cs{allFullClauses = new_afc}
    where new_afc = EMap.delete (clauseId cl) (allFullClauses cs)

clausesSize :: ClauseSet -> Int
clausesSize = CCS.size . clauses

{- nothingInClauses:
  returns True iff the Clauses set is empty
-}
nothingInClauses :: ClauseSet -> Bool
nothingInClauses = CCS.isEmpty . clauses


{- minInClauses:
  returns the minimum clause in the Clauses set (according to
  the complexity string) and removes it from Clauses.
  Clauses must be non-empty.
-}
minInClauses :: ClauseSet -> (ClauseSet, FullClause (At Opaque))
minInClauses cs = (removeFromIndexes cl cs{clauses = c'}, cl)
    where Just (cl, c') = CCS.minView (clauses cs)


{- oldestInClauses: Given
  returns the oldest clause in the Clauses set and removes it from Clauses
  Clauses must be non-empty
-}
oldestInClauses :: ClauseSet -> (ClauseSet, FullClause (At Opaque))
oldestInClauses cs = (removeFromIndexes cl cs{clauses = c'}, cl)
    where Just (cl, c') = CCS.oldView (clauses cs)

-------------------------------------------------------------------------------
-- InUse clauses set                                                         --
-------------------------------------------------------------------------------

{- addToInUse:
  adds cl to InUse. As a precondition, cl
  must have been formerly part of the clause set
-}
addToInUse ::  FullClause (At f) -> ClauseSet -> ClauseSet
addToInUse cl cs = cs{inUse          = IU.add cl (inUse cs),
                      allFullClauses = EMap.insert (clauseId cl)
                                                   (InUse, opaqueClause cl)
                                                   (allFullClauses cs)
                    }

{- removeFromInUse:
  removes cl from the in-use set
-}
removeFromInUse :: FullClause (At f) -> ClauseSet -> ClauseSet
removeFromInUse cl cs = removeFromIndexes cl cs{inUse = IU.remove cl (inUse cs)}


removeClauseById :: ClauseId
                 -> ClauseSet
                 -> (ClauseSet, Maybe (FullClause (At Opaque)))
removeClauseById clId cs = result
    where (location, fullClause) = if EMap.member clId (allFullClauses cs) then allFullClauses cs ! clId else (None, fullClause)
          result = case location of
                    Clauses -> (removeFromClauses fullClause cs, Just fullClause)
                    InUse   -> (removeFromInUse   fullClause cs, Just fullClause)
		    None    -> (cs, Nothing)


-------------------------------------------------------------------------------
-- Show                                                                      --
-------------------------------------------------------------------------------

instance Show ClauseSet where
    show cs = unlines [show $ clauses cs, "", IU.showPretty $ inUse cs]
