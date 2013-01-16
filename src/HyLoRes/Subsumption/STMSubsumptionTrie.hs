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

module HyLoRes.Subsumption.STMSubsumptionTrie(
    STMSubsumptionTrie, empty, add, subsumes, showTrie)

where


import Data.List ( sort)

import HyLoRes.Formula.Rep       ( IFormula )
import HyLoRes.Clause.FullClause ( FullClause, toIFormulaList )

import Control.Concurrent.STM

data STMSubsumptionTrie = Nil
                     | Node{val   :: TVar IFormula,
                            left  :: TVar STMSubsumptionTrie,
                            right :: TVar STMSubsumptionTrie,
                            next  :: TVar STMSubsumptionTrie}

showTrie :: STMSubsumptionTrie -> STM String
showTrie Nil = return "o"
showTrie trie = do v <- readTVar (val trie)
                   l <- readTVar (left trie)
                   r <- readTVar (right trie)
                   n <- readTVar (next trie)
                   lp <- showTrie l
                   rp <- showTrie r
                   np <- showTrie n
                   return $ "(N "++ show v ++ " " ++ lp ++ " " ++ rp ++ " " ++ np ++ ")"

empty :: STMSubsumptionTrie
empty = Nil


add :: FullClause f -> TVar STMSubsumptionTrie -> STM ()
add = addSortedList . asSortedList

asSortedList :: FullClause f -> [IFormula]
asSortedList = sort . toIFormulaList

addSortedList :: [IFormula] -> TVar STMSubsumptionTrie -> STM ()
addSortedList []       trieRef   = writeTVar trieRef Nil -- the empty clause subsumes all! (possible trie prunning)
addSortedList lst@(x:xs) trieRef = do st <- readTVar trieRef
                                      case st of
                                        Nil -> do v <- newTVar x
                                                  l <- newTVar Nil
                                                  r <- newTVar Nil
                                                  n <- newTVar Nil
                                                  writeTVar trieRef (Node v l r n)
                                                  addSortedList xs n
                                        _   -> do res <- readTVar (val st)
                                                  case compare x res of
                                                    EQ -> do n <- readTVar (next st)
                                                             if isNil n
                                                               then return ()  -- subsumed by the current clause
                                                               else addSortedList xs (next st)
                                                    LT -> addSortedList lst  (left  st)
                                                    GT -> addSortedList lst  (right st)

--addSortedList l        Nil = foldr (\i st -> Node i Nil Nil st) Nil l

subsumes :: TVar STMSubsumptionTrie -> FullClause f -> STM (Bool)
subsumes st  = subsumesSL st . asSortedList

subsumesSL :: TVar STMSubsumptionTrie -> [IFormula] -> STM (Bool)
subsumesSL _    []      = return False
subsumesSL trieRef l@(x:xs) = do st <- readTVar trieRef
                                 if isNil st
                                  then return False  -- the empty set of clauses subsumes nothing
                                  else do
                                          res <-readTVar (val st)
                                          case compare x res of
                                            EQ -> do nst <- readTVar (next st)
                                                     if isNil nst
                                                      then return True   -- end of branch, subsumed! or
                                                      else do subsumed <- subsumesSL (next st) xs -- subsumer contains x, or
                                                              if subsumed
                                                               then return True
                                                               else subsumesSL (right st) xs    -- subsumer does not contains x
                                                                  --
                                            LT -> do nfor <- (nodeFor x (left st))
                                                     subsumed <- subsumesSL nfor l
                                                     if subsumed
                                                      then return True           -- subsumer contains x, or
                                                      else subsumesSL trieRef xs      -- subsumer does not contains x
                                                                             --
                                            GT -> subsumesSL (right st) l -- nothing to do here, moving right

isNil :: STMSubsumptionTrie -> Bool
isNil Nil = True
isNil _   = False

nodeFor :: IFormula -> TVar STMSubsumptionTrie -> STM (TVar STMSubsumptionTrie)
nodeFor x trieRef  = do st <- readTVar trieRef
                        if isNil st
                          then return trieRef
                           else do
                                   res <- readTVar (val st)
                                   case compare x res of
                                     EQ -> return trieRef
                                     LT -> nodeFor x (left st)
                                     GT -> nodeFor x (right st)


