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

module HyLoRes.Subsumption.CASSubsumptionTrie(
    CASSubsumptionTrie, empty, add, subsumes
    )

where

import HyLoRes.Formula    ( HashOrd(..) )
import HyLoRes.Formula.NF ( AtFormulaNF )

import HyLoRes.Clause ( toFormulaList )
import HyLoRes.Clause.FullClause ( FullClause )

import Data.IORef

data CASSubsumptionTrie = Nil
                        | Node{val   :: HashOrd AtFormulaNF,
                               left  :: IORef CASSubsumptionTrie,
                               right :: IORef CASSubsumptionTrie,
                               next  :: IORef CASSubsumptionTrie}

empty :: CASSubsumptionTrie
empty = Nil

asSortedList :: FullClause f -> [HashOrd AtFormulaNF]
asSortedList = map HashOrd . toFormulaList

add :: FullClause f ->  IORef CASSubsumptionTrie -> IO ()
add = addSortedList . asSortedList

addSortedList :: [HashOrd AtFormulaNF] -> IORef CASSubsumptionTrie -> IO ()
addSortedList [] trieRef = writeIORef trieRef Nil -- the empty clause subsumes
                                                  -- all! (possible prunning)
addSortedList lst@(x:xs) trieRef =
    do st <- readIORef trieRef
       case st of
           Nil    -> do l <- newIORef Nil
                        r <- newIORef Nil
                        n <- newIORef Nil
                        b <- atomCAS trieRef (Node x l r n)
                        if b
                            then do addSortedList xs n
                            else do addSortedList lst trieRef
           Node{} -> case compare x (val st) of
                         EQ -> do n <- readIORef (next st)
                                  if isNil n
                                      then return () -- subsumed by the
                                                     -- current clause
                                      else addSortedList xs (next st)
                         LT -> addSortedList lst (left  st)
                         GT -> addSortedList lst (right st)

subsumes :: IORef CASSubsumptionTrie -> FullClause f -> IO (Bool)
subsumes st  = subsumesSL st . asSortedList

subsumesSL :: IORef CASSubsumptionTrie -> [HashOrd AtFormulaNF] -> IO (Bool)
subsumesSL _    []      = return False
subsumesSL trieRef l@(x:xs) =
  do st <- readIORef trieRef
     if isNil st
       then return False  -- the empty set of clauses subsumes nothing
       else case compare x (val st) of
             EQ -> do nst <- readIORef (next st)
                      if isNil nst
                       then return True           -- end of branch, subsumed! or
                       else                       -- subsumer contains x, or
                            do subsumed <- subsumesSL (next st) xs
                               if subsumed
                                 then return True
                                 else            -- subsumer does not contain x
                                      subsumesSL (right st) xs
             --
             LT -> do nfor <- (nodeFor x (left st))
                      subsumed <- subsumesSL nfor l
                      if subsumed
                        then return True           -- subsumer contains x, or
                        else subsumesSL trieRef xs -- it does not contains x
             --
             GT -> subsumesSL (right st) l -- nothing to do here, moving right

isNil :: CASSubsumptionTrie -> Bool
isNil Nil = True
isNil _   = False

nodeFor :: (HashOrd AtFormulaNF)
        -> IORef CASSubsumptionTrie
        -> IO (IORef CASSubsumptionTrie)
nodeFor x trieRef  = do st <- readIORef trieRef
                        if isNil st
                          then return trieRef
                           else do
                                   case compare x (val st) of
                                     EQ -> return trieRef
                                     LT -> nodeFor x (left st)
                                     GT -> nodeFor x (right st)


atomCAS :: IORef CASSubsumptionTrie -> CASSubsumptionTrie -> IO Bool
atomCAS ptr new = atomicModifyIORef ptr f
    where f cur = if isNil cur then  (new, True) else  (cur, False)
