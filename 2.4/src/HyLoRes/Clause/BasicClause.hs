----------------------------------------------------
--                                                --
-- HyLoRes.Clause.BasicClause.hs:                 --
-- A clause formed of formulas with no            --
-- additional information nor optimized           --
-- operations                                     --
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
module HyLoRes.Clause.BasicClause(BasicClause,
                                  emptyClause, singletonClause,
                                  add, delete, unsafeDelete, union,
                                  fromList, mergeAllDiamonds,
                                  isTrivTaut,
                                  --
                                  unit_tests)

where

import Test.QuickCheck ( Arbitrary(..), Property, (==>) )
import HyLo.Test       ( UnitTest, runTest )

import Control.Monad          ( liftM, guard )
import Control.Monad.Identity ( runIdentity )

import Data.List ( sortBy, nub, nubBy, foldl', (\\) )
import qualified Data.List as L

import Data.Map ( Map )
import qualified Data.Map as Map

import Data.Hash

import Text.Read ( Read(readPrec) )

import HyLoRes.Util.Classify ( classifyListBy, criteria2 )
import HyLoRes.Util.Ordering ( flipOrd )

import HyLoRes.Formula ( Formula, AtFormula, At, Diam, Top, Opaque,
                         NomSym, PropSym, RelSym,
                         at, top, nom, inputNom, prop, neg, diam, takeDisj,
                         opaque,
                         subf, onSubf, label, relSym,
                         specialize )

import HyLoRes.Formula.TypeLevel ( Spec(..) )

import HyLoRes.Formula.NF ( AtFormulaNF, nf, fromNF )

import HyLoRes.Formula.Util ( isTrivTrue, isTrivFalse )

import HyLoRes.Clause ( Clause(..) )

import HyLo.Signature ( HasSignature(..), emptySignature, merge )
import HyLo.Model     ( ModelsRel(..), Model )

data BasicClause = TrivTaut
                 | BC Int (Map Hash [AtFormulaNF])
                   deriving Eq

isTrivTaut :: BasicClause -> Bool
isTrivTaut TrivTaut = True
isTrivTaut _        = False

instance Clause BasicClause where
    isEmpty = null . toFormulaList

    size    TrivTaut = 1
    size    (BC s _) = s

    contains (BC _ fs)  f = maybe False ((nf f) `elem`) $ Map.lookup (hash f) fs
    contains c@TrivTaut f = [nf f] == toFormulaList c

    subset c c' = c `subsetEq` c' && size c < size c'

    subsetEq TrivTaut TrivTaut = True
    subsetEq (BC _ _) TrivTaut = False
    subsetEq TrivTaut (BC _ _) = False
    subsetEq (BC _ l) (BC _ r) = Map.null $ Map.differenceWith diffForms l r
        where diffForms fs gs = let d = fs \\ gs
                                in if null d then Nothing -- remove key
                                             else Just d

    toFormulaList TrivTaut  = [nf $ at (inputNom 0) top]
    toFormulaList (BC _ fs) = concat  $ Map.elems fs

instance Ord BasicClause where
    -- the ordering on clause must be the multiset extension of the
    -- ordering on formulas.
    compare c1 c2 = compare (revSorted c1) (revSorted c2)
        where revSorted = sortBy (\a b -> flipOrd $ compare a b) . toFormulaList

instance Show BasicClause where
    showsPrec _ = showList . toFormulaList

instance Read BasicClause where
    readPrec = (fromList :: [AtFormula] -> BasicClause) `liftM` readPrec

instance HasSignature BasicClause where
    type NomsOf  BasicClause = NomSym
    type PropsOf BasicClause = PropSym
    type RelsOf  BasicClause = RelSym
    getSignature = foldl' f emptySignature . toFormulaList
        where f a b = a `merge` (getSignature b)

instance Ord w
      => ModelsRel (Model w NomSym PropSym RelSym)
                   BasicClause NomSym PropSym RelSym where
    m |= cl = or [m |= f | f <- toFormulaList cl]

emptyClause :: BasicClause
emptyClause   = BC 0 Map.empty

{-
    Creates a singleton clause only if the formula is not trivially false
   (the empty clause is generated, otherwise)
-}
singletonClause :: Formula (At f) -> BasicClause
singletonClause f
    | isTrivFalse f = emptyClause
    | isTrivTrue  f = TrivTaut
    | otherwise     = BC 1 (Map.singleton (hash f') [f'])
        where f' = (nf f)

{-
    Adds a formula to the clause, only if is not trivially false
-}
add :: Formula (At f) -> BasicClause -> BasicClause
add = addNF . nf

addNF :: AtFormulaNF -> BasicClause -> BasicClause
addNF _ c@TrivTaut = c
addNF f c@(BC s m)
    | isTrivFalse (fromNF f)  = c
    | isTrivTrue  (fromNF f) ||
      safeMakesItTrivTrue f c = TrivTaut
    | otherwise               = c'
  where c' = let (o,m') = Map.insertLookupWithKey (const L.union) h [f] m
                 mlen   = maybe 0 length
                 s'     = s + (mlen (Map.lookup h m') - mlen o)
                 h      = hash f
             in BC s' m'

-- HUGE WARNING: One cannot discard clauses of the form {@ij, @i-j} U C
-- nor {@i<>Fj, @i[]-j} U C without compromising completeness!
-- This is because although they are tautologies, they are not neccesarily
-- tr-tautologies (i.e. tautologies after applying the tr function to their
-- formulas). See the completeness proof for the details, and/or take a look
-- at unsat/test35.frm for an eloquent example

safeMakesItTrivTrue :: AtFormulaNF -> BasicClause -> Bool
safeMakesItTrivTrue _  TrivTaut = True
safeMakesItTrivTrue f  c        = isSafe && c `contains` (neg $ fromNF f)
    where isSafe  = isSafeToTestTrivTrue (fromNF f)

isSafeToTestTrivTrue :: AtFormula -> Bool
isSafeToTestTrivTrue f = case specialize f of
                             AtNom{}     -> False
                             AtNegNom{}  -> False
                             AtDiamNom{} -> False
                             AtBoxF f'   -> not (isRel $ neg f')
                             _           -> True
    where isRel r = case specialize r of { AtDiamNom{} -> True; _ -> False }

union :: BasicClause -> BasicClause -> BasicClause
union c = foldl' (flip addNF) c . toFormulaList

delete :: Formula (At f) -> BasicClause -> BasicClause
delete = delUsing listDel

listDel :: AtFormulaNF -> [AtFormulaNF] -> Maybe [AtFormulaNF]
listDel f fs = do let fs' = L.delete f fs
                  guard ( not $ null fs')
                  return fs'

-- Just like delete but with the precondition that the formula
-- to be deleted *must occur* in the clause
unsafeDelete :: Formula (At f) -> BasicClause -> BasicClause
unsafeDelete = delUsing fastUnsafeDel
    where fastUnsafeDel _ [_] = Nothing  -- only one formula, this is it!
          fastUnsafeDel f fs  = listDel f fs

delUsing :: (AtFormulaNF -> [AtFormulaNF] -> Maybe [AtFormulaNF])
         -> Formula (At f)
         -> BasicClause
         -> BasicClause
delUsing _ f TrivTaut = if TrivTaut `contains` f then emptyClause else TrivTaut
delUsing d f (BC s m) = let m'  = Map.update (d $ nf f)  (hash f) m
                            s'  = s + (len m' - len m)
                            len = maybe 0 length . (Map.lookup (hash f))
                        in BC s' m'


fromList :: [Formula (At f)] -> BasicClause
fromList = fromListNF . map nf

fromListNF ::[AtFormulaNF] -> BasicClause
fromListNF = foldl' (flip addNF) emptyClause


{- mergeAllDiamonds: Given

  - a BasicClause cl

  Formulas of the form @_n<r>F_i (1 <= i <= k, F_i is not a nominal)
  are merged in a formula @_n<r>(F_1 v ... v F_k). This should avoid
  the generation of too many new nominals (is this really the case?)

  Observe that, by construction, no BasicClause contain
  formulas of the form @n -n nor @n -True, nor two complementary
  literals
-}
mergeAllDiamonds :: BasicClause -> BasicClause
mergeAllDiamonds c@TrivTaut = c
mergeAllDiamonds c =
    runIdentity $ do
      let fs = toFormulaList c
      (theRest, dias) <- return $ mapPartition complexDia fs
      if null dias
        then return c
        else do let classify = classifyListBy (criteria2 label (relSym . subf))
                groupedForms <- return $ classify dias
                let groups = Map.elems groupedForms
                finalForms   <- return $ map mergeDiamonds groups
                return $ fromListNF (theRest ++ finalForms)

complexDia :: AtFormulaNF -> Maybe (Formula (At (Diam Opaque)))
complexDia f = case specialize (fromNF f) of
                   AtDiamF f' -> (Just . onSubf (onSubf opaque)) f'
                   _          -> Nothing

mapPartition :: (a -> Maybe b) -> [a] -> ([a], [b])
mapPartition _ []     = ([], [])
mapPartition f (x:xs) = maybe (x:as, bs) (\b -> (as, b:bs)) (f x)
    where (as,bs) = mapPartition f xs

{- mergeDiamonds: Given

    - a nonempty list of formulas of the form [@i<r>f1, ..., @i<r>fn]
      (fi is not a nominal)

    returns the formula @i<r>(f1 v .... v fn)
-}
mergeDiamonds :: [Formula (At (Diam Opaque))] -> AtFormulaNF
mergeDiamonds    [f]   = nf f
mergeDiamonds fs@(f:_) = nf $ onSubf (onSubf $ \_ -> takeDisj fs_diam_args) f
  where fs_diam_args = map (subf . subf) fs
mergeDiamonds    _     = error "mergeDiamonds: Can't happen"

-- -----------------------------------------------------
-- -- QuickCheck stuff
-- -----------------------------------------------------

-- this requires undecidable instances
instance Arbitrary BasicClause where
    arbitrary   = fromListNF `liftM` arbitrary
    coarbitrary = coarbitrary . toFormulaList

prop_singletonTautGetTaut :: Formula (At Top) -> Bool
prop_singletonTautGetTaut f = isTrivTaut $ singletonClause f

prop_singletonInvalidGetEmpty :: NomSym -> Bool
prop_singletonInvalidGetEmpty i = isEmpty $ singletonClause trivFalse
    where trivFalse = at i (neg $ nom i)

prop_addTautGetTaut :: BasicClause -> Formula (At Top) -> Bool
prop_addTautGetTaut c f = isTrivTaut $ add f c

prop_addTrivEqGetTaut :: BasicClause -> NomSym -> Bool
prop_addTrivEqGetTaut c i = isTrivTaut $ add trivEq c
    where trivEq = at i (nom i)

prop_addInvalidGetSame :: BasicClause -> NomSym -> Bool
prop_addInvalidGetSame c i = add trivFalse c == c
    where trivFalse = at i (neg $ nom i)

prop_neg_isSafeToTestTrivTrue :: AtFormula -> Bool
prop_neg_isSafeToTestTrivTrue f = isSafeToTestTrivTrue (neg f) ==
                                  isSafeToTestTrivTrue f


prop_addNegationOfSomeGetTaut :: BasicClause -> AtFormula -> Bool
prop_addNegationOfSomeGetTaut c f
    | isSafeToTestTrivTrue f = isTrivTaut $ add (neg f) (add f c)
    | isTrivTrue (neg f)     = isTrivTaut $ add (neg f) (add f c)
    | otherwise              = (isTrivTaut $ add (neg f) (add f c)) ==
                               (isTrivTaut $ add f c)


prop_union :: [AtFormulaNF] -> [AtFormulaNF] -> Bool
prop_union l1 l2 = (fromListNF l1 `union` fromListNF l2) == fromListNF (l1++l2)

prop_read :: BasicClause -> Bool
prop_read c = c == (read . show $ c)

prop_subsetEq_ref :: BasicClause -> Bool
prop_subsetEq_ref c = c `subsetEq` c

prop_subsetEq_subset :: BasicClause -> BasicClause -> Bool
prop_subsetEq_subset c d = c `subsetEq` d == (c `subset` d || c == d)

prop_subset_irref :: BasicClause -> BasicClause -> Bool
prop_subset_irref c d = not (c `subset` d && d `subset` c)

prop_subset_union :: BasicClause -> BasicClause -> Property
prop_subset_union c d = and [not (isTrivTaut c_U_d), notEmpty c, notEmpty d]
                    ==> c `subset` c_U_d && d `subset` c_U_d
    where c_U_d = c `union` d
          notEmpty = not . isEmpty

prop_size_add :: BasicClause -> AtFormula -> Bool
prop_size_add  c f = size c' == (length $ toFormulaList c')
    where c' = add f c

prop_size_delete :: BasicClause -> AtFormula -> Bool
prop_size_delete  c f = size c' == (length $ toFormulaList c')
    where c' = delete f c

prop_size_union :: BasicClause -> BasicClause -> Bool
prop_size_union c d = size c_U_d == (length $ toFormulaList c_U_d)
    where c_U_d = c `union` d

prop_unsafeDelete :: BasicClause -> Bool
prop_unsafeDelete c = and [unsafeDelete f c == delete f c | f <- c_forms]
    where c_forms = map fromNF $ toFormulaList c

newtype AtDiaForms = AtDiaForms (NomSym, RelSym, [Formula Opaque])
                      deriving (Eq, Show, Read)

forms      :: AtDiaForms -> [Formula Opaque]
asFormula  :: AtDiaForms ->  Formula (At (Diam Opaque))
distrAtDia :: AtDiaForms -> [Formula (At (Diam Opaque))]
prefNom    :: AtDiaForms -> NomSym

forms      (AtDiaForms (_, _, fs)) = fs
asFormula  (AtDiaForms (i, r,[f])) = at i $ diam r f
asFormula  (AtDiaForms (i, r, fs)) = at i . diam r . opaque $ takeDisj fs
distrAtDia (AtDiaForms (i, r, fs)) = map (at i . diam r) fs
prefNom    (AtDiaForms (i, _, _))  = i

instance Arbitrary AtDiaForms where
    arbitrary = do n  <- arbitrary
                   r  <- arbitrary
                   fs <- arbitrary
                   let notNom f = case specialize (at n $ f) of
                                      { AtNom{} -> False; _ -> True }
                   let nonRels = filter notNom
                   let fs' = nonRels fs
                   if null fs'
                     then do p <- arbitrary
                             return $ AtDiaForms (n, r, [opaque $ prop p])
                     else return $ AtDiaForms (n, r, nub fs')
    --
    coarbitrary = undefined

prop_mergeDiamonds :: AtDiaForms -> Bool
prop_mergeDiamonds x = case spec $ mergeDiamonds (distrAtDia x) of
                         AtDiamF f -> f == asFormula x
                         _         -> False
    where spec = specialize . fromNF

prop_mergeAllDiamonds :: [AtDiaForms] -> Bool
prop_mergeAllDiamonds xs =
                 (fromList $ map asFormula xs') ==
                   (mergeAllDiamonds . fromList . concatMap distrAtDia $ xs')
    where xs' = nubBy (\a b -> prefNom a == prefNom b)
                      (filter (not . null . forms) xs)

unit_tests :: UnitTest
unit_tests = [
    ("singleton taut is taut",          runTest prop_singletonTautGetTaut),
    ("singleton invalid is taut",       runTest prop_singletonInvalidGetEmpty),
    ("add a taut, get a taut",          runTest prop_addTautGetTaut),
    ("isSafeToTestTrivTrue closed neg", runTest prop_neg_isSafeToTestTrivTrue),
    ("add a trivial eq, get a taut",    runTest prop_addTrivEqGetTaut),
    ("add invalid, get the same",       runTest prop_addInvalidGetSame),
    ("add negation of prev, get taut",  runTest prop_addNegationOfSomeGetTaut),
    ("union works",                     runTest prop_union),
    ("read/show",                       runTest prop_read),
    ("subsetEq is reflexive",           runTest prop_subsetEq_ref),
    ("subsetEq by def",                 runTest prop_subsetEq_subset),
    ("subset is irreflexive",           runTest prop_subset_irref),
    ("subset works well with unions",   runTest prop_subset_union),
    ("size works after add",            runTest prop_size_add),
    ("size works after delete",         runTest prop_size_delete),
    ("size works after union",          runTest prop_size_union),
    ("unsafeDelete is like delete",     runTest prop_unsafeDelete),
    ("mergeDiamonds works",             runTest prop_mergeDiamonds),
    ("mergeAllDiamonds works",          runTest prop_mergeAllDiamonds)
  ]
