----------------------------------------------------
--                                                --
-- HyLoRes.ClauseSet.Clauses:                     --
-- A set of FullClauses ordered by complexity.    --
-- They can also be retrieved by age              --
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

module HyLoRes.ClauseSet.Clauses(
    -- types
    ClausesClauseSet, ComplexityParamStr,

    -- constructors
    newSet,

    -- manipulators
    add, removeById, minView, oldView,

    -- observers
    isEmpty, size, containsClause,

    -- unit tests
    unit_tests
) where

import Test.QuickCheck ( Arbitrary(..), sized, elements, oneof, variant )
import HyLo.Test       ( UnitTest, runTest )

import Control.Monad       ( when, guard, liftM )
import Control.Monad.State ( State, runState, get, put, gets, modify )

import Data.List (foldl', sort, sortBy, insert, delete)

import Data.Map ( Map )
import qualified Data.Map as Map

import Data.Foldable ( toList )
import Data.Sequence ( Seq, (|>), ViewL(..) )
import qualified Data.Sequence as Seq

import Data.EnumMap ( EnumMap )
import qualified Data.EnumMap as IMap


import HyLoRes.Util ( ShowRight(..), commaSeparateHdr, compareUsing,
                      adjustOrInsert, filterFirst )

import HyLo.Formula    ( Formula(Prop, Nom, Diam, Box), composeFold )
import HyLoRes.Formula ( At, Opaque, level, label, unNNF )

import HyLoRes.Formula.NF ( fromNF )

import qualified HyLoRes.Clause as C
import HyLoRes.Clause.FullClause ( FullClause, ClauseId,
                                   clauseId, distFormula, specialize )
import HyLoRes.Formula.TypeLevel ( Spec(..) )

type ClauseComplexity = [Int]
type ComplexityParamStr = String

type Age = Int

type OpaqueFullClause = FullClause (At Opaque)

data ClausesClauseSet = CCS{
      queuesByComplexity :: Map ClauseComplexity (Seq (OpaqueFullClause, Age)),
      clauseDataByAge    :: Map Age (ClauseId, ClauseComplexity),
                            -- can't use IntMap here because it lacks
                            -- findMin-related functions!
      clauseDataById     :: EnumMap ClauseId (Age, ClauseComplexity),
      nextTimestamp      :: Age,
      complexityOf       :: OpaqueFullClause -> ClauseComplexity
    }

instance Show ClausesClauseSet where
    show  ccs = (commaSeparateHdr "Clauses: { " show_clauses) ++ " }"
        where show_clauses = map (ShowRight . show) $ asFullClauseList ccs

asFullClauseList :: ClausesClauseSet -> [OpaqueFullClause]
asFullClauseList = map fst . concatMap toList  . Map.elems . queuesByComplexity


newSet :: ComplexityParamStr -> ClausesClauseSet
newSet p = CCS{queuesByComplexity = Map.empty,
               clauseDataByAge    = Map.empty,
               clauseDataById     = IMap.empty,
               nextTimestamp      = 0,
               complexityOf       = buildComplexity p}

add :: FullClause (At Opaque) -> ClausesClauseSet -> ClausesClauseSet
add cl ccs = ccs{queuesByComplexity = adjustOrInsert addCl c newQueue qbc,
                 clauseDataByAge    = Map.insert ts (clId, c) dba,
                 clauseDataById     = IMap.insert (clauseId cl) (ts, c) dbi,
                 nextTimestamp      = ts + 1}
        where addCl    = (|> (cl, ts))
              c        = complexityOf ccs cl
              newQueue = Seq.singleton (cl, ts)
              qbc      = queuesByComplexity ccs
              dba      = clauseDataByAge ccs
              dbi      = clauseDataById ccs
              ts       = nextTimestamp ccs
              clId     = clauseId cl


minView :: ClausesClauseSet -> Maybe (FullClause (At Opaque), ClausesClauseSet)
minView ccs =
    do guard (not . isEmpty $ ccs)
       --
       let qbc = queuesByComplexity ccs
       let cba = clauseDataByAge ccs
       let cbi = clauseDataById ccs
       --
       let ((_, q), qbc')      = Map.deleteFindMin qbc
       let (minCl, age) :<  q' = Seq.viewl q
       --
       let ccs' = ccs{clauseDataByAge = Map.delete age cba,
                      clauseDataById  = IMap.delete (clauseId minCl) cbi}
       --
       return $ if Seq.null q'
           then (minCl, ccs'{queuesByComplexity = qbc'})
           else (minCl,
                 ccs'{queuesByComplexity = Map.updateMin (const (Just q')) qbc})

oldView :: ClausesClauseSet -> Maybe (FullClause (At Opaque), ClausesClauseSet)
oldView ccs =
    do guard (not . isEmpty $ ccs)
       --
       let qbc = queuesByComplexity ccs
       let cba = clauseDataByAge ccs
       let cbi = clauseDataById ccs
       --
       let ((_, (i,c)), cba') = Map.deleteFindMin cba
       q <- Map.lookup c qbc
       let (oldCl,_) :< q' = Seq.viewl q
       --
       let ccs' = ccs{clauseDataByAge = cba',
                      clauseDataById  = IMap.delete i cbi}
       return $ if Seq.null q'
         then (oldCl, ccs'{queuesByComplexity = Map.delete c qbc})
         else (oldCl, ccs'{queuesByComplexity = Map.insert c q' qbc})


removeUpdate :: ClauseId
             -> Seq (OpaqueFullClause, Age)
             -> Maybe (Seq (OpaqueFullClause, Age))
removeUpdate clId q =
    do let newList = filterFirst ((clId ==) . clauseId . fst) . toList $ q
       guard (not . null $ newList)
       return $ Seq.fromList newList

removeById :: ClauseId -> ClausesClauseSet -> ClausesClauseSet
removeById clId ccs = ccs{queuesByComplexity = qbc',
                          clauseDataByAge    = cba',
                          clauseDataById     = cbi'}
    where mac  = IMap.lookup clId cbi
          cba  = clauseDataByAge ccs
          cba' = maybe cba (\(a,_) -> Map.delete a cba) mac
          cbi  = clauseDataById ccs
          cbi' = IMap.delete clId cbi
          qbc  = queuesByComplexity ccs
          qbc' = maybe qbc (\(_,c) -> Map.update (removeUpdate clId) c qbc) mac

containsClause :: ClauseId -> ClausesClauseSet -> Bool
containsClause clId = IMap.member clId . clauseDataById

isEmpty :: ClausesClauseSet -> Bool
isEmpty = IMap.null . clauseDataById


size :: ClausesClauseSet -> Int
size = IMap.size . clauseDataById


{------------------------------------------------------------}
{- Complexity calculation                                   -}
{------------------------------------------------------------}

{- buildComplexity: Given

 - a ComplexityParamStr p, i.e. a String formed of 's', 'v', 'V',
   'd', 'D', 'l', 'L', 'M', 'B'; the clause will be priorized according
   to this key:

   + 's' means the size of the clause,
   + 'v' means the sum of the number of [not necessarily distinct] atoms
     in the formulas of the clause,
   + 'V' means the number of [not necessarily distinct] atoms in
         the distinguished formula
   + 'd' means the maximum modalDepth of a formula,
   + 'D' means the modalDepth of the distinguished formula,
   + 'l' means the minimum level of the prefix of a formula in the clause
   + 'L' means the level of the prefix of the distinguished formula (the
      smaller the level, the bigger the priority)
   + 'M' means '1' if the distinguished formula is of the form @_n<>A and
      A is not a nominal, or '0' otherwise
   + 'B' means '1' if the distinguished formula is of the form @_n[]A, or
      '0' otherwise

 - a FullClause c

  returns the ClauseComplexity of c parameterized by p.
-}
buildComplexity :: ComplexityParamStr
                -> FullClause (At Opaque)
                -> ClauseComplexity
buildComplexity p = \c -> [metric c | metric <- map c2m p]
    where c2m 's' = C.size
          c2m 'v' = foldl' (flip $ (+) . countAtoms . unNNF )    0 . formList
          c2m 'V' = countAtoms .   unNNF . distFormula
          c2m 'd' = foldl' (flip $ max . formulaDepth . unNNF)   0 . formList
          c2m 'D' = formulaDepth . unNNF . distFormula
          c2m 'l' = foldl' (flip $ max . level . label) 0 . formList
          c2m 'L' = level . label . distFormula
          c2m 'M' = \c -> case specialize c of { AtDiamF{} -> 1; _ -> 0 }
          c2m 'B' = \c -> case specialize c of { AtBoxF{} -> 1; _ -> 0 }
          c2m _   = error $ "Clauses.buildComplexity: Malformed string " ++
                            "specifying order for selection of given clause."
          formList = map fromNF . C.toFormulaList

countAtoms :: Formula nom prop rel -> Int
countAtoms (Prop _) = 1
countAtoms (Nom  _) = 1
countAtoms  f       = composeFold 0 (+) countAtoms f

formulaDepth :: Formula nom prop rel -> Int
formulaDepth (Diam _ f) = 1 + formulaDepth f
formulaDepth (Box  _ f) = 1 + formulaDepth f
formulaDepth  f         = composeFold 0 max formulaDepth f


-----------------------------------------------------
-- QuickCheck stuff
-----------------------------------------------------

unit_tests :: UnitTest
unit_tests = [("behaves like ref impl", runTest prop_sameAsRefImpl)]

prop_sameAsRefImpl :: RandomComplexityStr -> [TestAction] -> Bool
prop_sameAsRefImpl rcs actions = resultsCCS == resultsL &&
                                 sort (asFullClauseList ccs) ==
                                 sort (asFullClauseListL ref)
    where compl       = unRCS rcs
          (resultsCCS, ccs) = runActions action  actions (newSet compl)
          (resultsL,   ref) = runActions actionL actions (newSetL compl)

newtype RandomComplexityStr = RCS{unRCS:: ComplexityParamStr} deriving Show

instance Arbitrary RandomComplexityStr where
    arbitrary   = liftM RCS $ sized f
        where f n = sequence . replicate n $ elements "svVdDlLMB"
    --
    coarbitrary = coarbitrary . map fromEnum . unRCS

data TestAction = Add OpaqueFullClause
                | MinView
                | OldView
                | Remove ClauseId
                | IsEmpty
                | Size
                  deriving Show

instance Arbitrary TestAction where
    arbitrary = oneof [Add    `liftM` arbitrary,
                       return MinView,
                       return OldView,
                       Remove `liftM` arbitrary,
                       return IsEmpty,
                       return Size]
    --
    coarbitrary (Add cl)   = variant 0 . coarbitrary cl
    coarbitrary  MinView   = variant 1
    coarbitrary  OldView   = variant 2
    coarbitrary (Remove i) = variant 3 . coarbitrary i
    coarbitrary  IsEmpty   = variant 4
    coarbitrary  Size      = variant 5

data ActionResult = Void
                  | V (Maybe OpaqueFullClause)
                  | B Bool
                  | I Int
                    deriving(Eq, Show)

runView :: (a -> Maybe (OpaqueFullClause, a))
        -> State a (Maybe OpaqueFullClause)
runView f = do cs <- get
               case f cs of
                 Nothing       -> return Nothing
                 Just (c, cs') -> put cs' >> return (Just c)

action :: TestAction -> State ClausesClauseSet ActionResult
action (Add cl)   = do b <- gets (containsClause $ clauseId cl)
                       when (not b) $ do
                         modify (add cl)
                         return ()
                       return (B b)
action  MinView   = runView minView       >>= return . V
action  OldView   = runView oldView       >>= return . V
action (Remove i) = modify (removeById i) >>  return Void
action  IsEmpty   = gets isEmpty          >>= return . B
action  Size      = gets size             >>= return . I


runActions :: (TestAction -> State a ActionResult)
           -> [TestAction]
           -> a
           -> ([ActionResult], a)
runActions f as = runState (mapM f as)


{- Inefficient reference implementation based on a list;
   used to quickCheck functionality -}

type RefImpl = (OpaqueFullClause -> ClauseComplexity,
                [(ClauseComplexity, Order, OpaqueFullClause)])
type Order = Int

newSetL :: ComplexityParamStr -> RefImpl
newSetL s = (buildComplexity s, [])

addL :: OpaqueFullClause -> RefImpl -> RefImpl
addL cl (f, xs) = (f, insert (f cl, newer + 1, cl) xs)
    where newer = foldl' (flip $ max . snd2) 0 xs

minViewL :: RefImpl -> Maybe (OpaqueFullClause, RefImpl)
minViewL (_, [])     = Nothing
minViewL (f, (x:xs)) = Just (thr2 x, (f, xs))

oldViewL :: RefImpl -> Maybe (OpaqueFullClause, RefImpl)
oldViewL (_, []) = Nothing
oldViewL (f, xs) = let (x:_') = sortBy (compareUsing snd2) xs
                   in Just (thr2 x, (f, delete x xs))

removeByIdL :: ClauseId -> RefImpl -> RefImpl
removeByIdL clId (f, xs) = (f, (filter ((clId /=) . clauseId . thr2) xs))

isEmptyL :: RefImpl -> Bool
isEmptyL (_, xs) = null xs

sizeL :: RefImpl -> Int
sizeL (_, xs) = length xs

asFullClauseListL :: RefImpl -> [OpaqueFullClause]
asFullClauseListL (_, xs) = map thr2 xs

containsClauseL :: ClauseId -> RefImpl -> Bool
containsClauseL clId (_, xs) = clId `elem` map (clauseId . thr2) xs

snd2 :: (a, b, c) -> b
snd2 (_, x, _)  = x

thr2 :: (a, b, c) -> c
thr2 (_, _, x)  = x

actionL :: TestAction -> State RefImpl ActionResult
actionL (Add cl)   = do b <- gets (containsClauseL $ clauseId cl)
                        when (not b) $ do
                            modify (addL cl)
                            return ()
                        return (B b)
actionL MinView    = runView minViewL       >>= return . V
actionL OldView    = runView oldViewL       >>= return . V
actionL (Remove i) = modify (removeByIdL i) >>  return Void
actionL IsEmpty    = gets isEmptyL          >>= return . B
actionL Size       = gets sizeL             >>= return . I
