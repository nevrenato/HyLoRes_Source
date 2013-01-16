----------------------------------------------------
--                                                --
-- HyLoRes.Subsumption.SubsumptionTrie:           --
-- Structure to check if new clauses are subsumed --
-- by the set of clauses                          --
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

module HyLoRes.Subsumption.SubsumptionTrie(
    SubsumptionTrie, empty, add, subsumes,
    unit_tests)

where

import Data.List ( sort, subsequences )

import Test.QuickCheck
import HyLo.Test       ( UnitTest, runTest )

import HyLoRes.Formula          ( HashOrd(..), At, Opaque )
import HyLoRes.Formula.NF       ( AtFormulaNF )

import HyLoRes.Clause            ( toFormulaList )
import HyLoRes.Clause.FullClause ( FullClause )

data SubsumptionTrie = Nil
                     | Node{val   :: HashOrd AtFormulaNF,
                            left  :: !SubsumptionTrie,
                            right :: !SubsumptionTrie,
                            next  :: !SubsumptionTrie}
                    deriving (Read, Show)

empty :: SubsumptionTrie
empty = Nil

add :: FullClause f -> SubsumptionTrie -> SubsumptionTrie
add = addSortedList . asSortedList

asSortedList :: FullClause f -> [HashOrd AtFormulaNF]
asSortedList = sort . map HashOrd . toFormulaList

addSortedList :: [HashOrd AtFormulaNF] -> SubsumptionTrie -> SubsumptionTrie
addSortedList []       _   = Nil -- the empty clause subsumes all!
                                 -- (possible trie prunning)
addSortedList l        Nil = foldr (\i st -> Node i Nil Nil st) Nil l
addSortedList l@(x:xs) st  = case compare x (val st) of
                               EQ -> if isNil (next st)
                                      then st  -- subsumed by current clause
                                      else st{next = addSortedList xs (next st)}
                               LT -> st{left  = addSortedList l  (left  st)}
                               GT -> st{right = addSortedList l  (right st)}

subsumes :: SubsumptionTrie -> FullClause f -> Bool
subsumes st  = subsumesSL st . asSortedList

subsumesSL :: SubsumptionTrie -> [HashOrd AtFormulaNF] -> Bool
subsumesSL Nil  _       = False     -- the empty set of clauses subsumes nothing
subsumesSL _    []      = False
subsumesSL st  l@(x:xs) = case compare x (val st) of
                            EQ -> isNil (next st)
                                       -- end of branch, subsumed! or

                                  ||  subsumesSL (next  st) xs
                                       -- subsumer contains x or

                                  ||  subsumesSL (right st) xs
                                       -- subsumer does not contains x
                            --
                            LT -> subsumesSL (nodeFor x $ left  st) l
                                       -- subsumer contains x, or

                                  ||  subsumesSL st xs
                                       -- subsumer does not contains x
                            --
                            GT -> subsumesSL (right st) l
                                       -- nothing to do here, moving right

isNil :: SubsumptionTrie -> Bool
isNil Nil = True
isNil _   = False

nodeFor :: HashOrd AtFormulaNF -> SubsumptionTrie -> SubsumptionTrie
nodeFor _ Nil = Nil
nodeFor x st  = case compare x (val st) of
                  EQ -> st
                  LT -> nodeFor x (left st)
                  GT -> nodeFor x (right st)

clauses :: SubsumptionTrie -> [[HashOrd AtFormulaNF]]
clauses Nil = [[]]
clauses st = concat [map (val st :) (clauses $ next st),
                     filter (not . null) . clauses $ left st,
                     filter (not . null) . clauses $ right st]

contains :: SubsumptionTrie -> [HashOrd AtFormulaNF] -> Bool
contains Nil xs     = null xs
contains _   []     = False
contains st  (x:xs) = case (nodeFor x st) of
                        Nil -> False
                        st' -> contains (next st') xs


-----------------------------------
-- QuickCheck stuff
-----------------------------------

instance Arbitrary SubsumptionTrie where
    arbitrary = f `fmap` arbitrary
        where f :: [FullClause (At Opaque)] -> SubsumptionTrie
              f = foldr add Nil
    --
    coarbitrary Nil            = variant 0
    coarbitrary (Node v l r n) = variant 1
                               . coarbitrary (fromHashOrd v)
                               . coarbitrary l
                               . coarbitrary r
                               . coarbitrary n

prop_nodeForWorks :: SubsumptionTrie -> AtFormulaNF -> Bool
prop_nodeForWorks st f = case nodeFor hf st of
                            Nil -> isNil st || (not $ hf `elem` initials)
                            st' -> hf `elem` initials && val st' == hf
    where initials = map head (clauses st)
          hf       = HashOrd f

prop_containedClausesAreSubsumed :: SubsumptionTrie -> Bool
prop_containedClausesAreSubsumed st = isNil st ||
                                      all (subsumesSL st) (clauses st)

prop_containedClausesAreContained :: SubsumptionTrie -> Bool
prop_containedClausesAreContained st = all (contains st) (clauses st)

prop_subsumesIffSubclause :: SubsumptionTrie->FullClause (At Opaque)->Property
prop_subsumesIffSubclause st cl = classify isSubsumed "subsumed" $
                                       isSubsumed == subsumes st cl
    where isSubsumed = or $ map (contains st) (notNullSubseqs $ asSortedList cl)
          notNullSubseqs = filter (not . null) . subsequences

unit_tests :: UnitTest
unit_tests = [
  ("nodeFor works",                  runTest prop_nodeForWorks),
  ("contained clauses are subsumed", runTest prop_containedClausesAreSubsumed),
  ("contained clauses are contained",runTest prop_containedClausesAreContained),
  ("subsumes iff subclause",         runTest prop_subsumesIffSubclause)
  ]
