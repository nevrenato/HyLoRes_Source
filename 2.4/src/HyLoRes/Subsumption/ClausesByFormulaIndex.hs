--------------------------------------------------------------
--                                                          --
-- HyLoRes.Subsumption.ClausesByFormulaIndex:               --
-- This is an index that allows to retrieve the             --
-- id of all the clauses that contain a given               --
-- formula id. It implements a [hopefully] fast             --
-- backwards subsumption check.                             --
--                                                          --
--------------------------------------------------------------

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
module HyLoRes.Subsumption.ClausesByFormulaIndex(
    ClausesByFormulaIndex, SetOfClauseIds,
    emptyIndex,
    addToIndex, addToIndexLookupSubs,
    removeFromIndex)
where

import Control.Monad(guard)
import Control.Monad.State(State, runState, get, put)

import Data.Maybe(fromMaybe)
import Data.List(sortBy, foldl', foldl1')


import Data.Map ( Map )
import qualified Data.Map as Map ( empty, insertWith, insertLookupWithKey, update )

import Data.EnumSet ( EnumSet )
import qualified Data.EnumSet as Set ( empty, singleton,
                                       insert, delete, intersection,
                                       size, null )

import HyLoRes.Util ( compareUsing )

import HyLoRes.Formula    ( HashOrd(..) )
import HyLoRes.Formula.NF ( AtFormulaNF )
import HyLoRes.Clause ( Clause(..) )
import HyLoRes.Clause.FullClause ( FullClause, ClauseId, clauseId )

type SetOfClauseIds = EnumSet ClauseId

newtype ClausesByFormulaIndex = I (Map (HashOrd AtFormulaNF) SetOfClauseIds)


emptyIndex :: ClausesByFormulaIndex
emptyIndex = I Map.empty

addToIndex :: FullClause f -> ClausesByFormulaIndex -> ClausesByFormulaIndex
addToIndex cl (I cbf) = I $ foldl' (flip f) cbf (map HashOrd $ toFormulaList cl)
  where f frm = Map.insertWith (\_ -> Set.insert clId) frm (Set.singleton clId)
        clId  = clauseId cl

addToIndexLookupSubs :: FullClause f
                     -> ClausesByFormulaIndex
                     -> (SetOfClauseIds, ClausesByFormulaIndex)
addToIndexLookupSubs cl = runState go
  where go = do let clId  = clauseId cl
                let forms = toFormulaList cl
                subsCandidates <- mapM (insertLookupClause clId ) forms
                -- I will be using the fact that:
                -- "Intersection is more efficient on
                -- (bigset intersection smallset)."
                -- according to the Data.Set documentation
                let sortedCands = sortBy (compareUsing Set.size) subsCandidates
                return $! foldl1' (flip Set.intersection) sortedCands

insertLookupClause :: ClauseId
                   -> AtFormulaNF
                   -> State ClausesByFormulaIndex SetOfClauseIds
insertLookupClause c f =
    do I st <- get
       let (prev,st') = Map.insertLookupWithKey (\_ _ o->Set.insert c o)
                                                (HashOrd f)
                                                (Set.singleton c)
                                                st
       put (I st')
       return $ fromMaybe Set.empty prev

removeFromIndex :: FullClause f
                -> ClausesByFormulaIndex
                -> ClausesByFormulaIndex
removeFromIndex cl idx = foldl' (remove clId) idx forms
    where clId  = clauseId cl
          forms = map HashOrd (toFormulaList cl)

remove :: ClauseId
       -> ClausesByFormulaIndex
       -> HashOrd AtFormulaNF
       -> ClausesByFormulaIndex
remove clId (I cbfi) formulaId = I $ Map.update removeFromSet formulaId cbfi
    where removeFromSet s = do let s' = Set.delete clId s
                               guard ( not $ Set.null s' )
                               return s'
