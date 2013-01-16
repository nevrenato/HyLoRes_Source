----------------------------------------------------
--                                                --
-- HyLoRes.Clause.FullClause.hs:                  --
-- Clauses with access to maximum formula in      --
-- O(1), where the selection function was applied --
-- and with a clause identifier                   --
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

module HyLoRes.Clause.FullClause(FullClause, ClauseId,
                                 makeFullClause, opaqueClause,
                                 clauseId,
                                 selectedFormula, distFormula, occursNom,
                                 splitAtDist,
                                 --
                                 specialize,
                                 --
                                 unit_tests)

where

import Test.QuickCheck ( Arbitrary(..), sized, elements )
import HyLo.Test       ( UnitTest, runTest )

import Data.Maybe ( fromMaybe, isJust )
import Data.List  ( sort )

import Text.Read                    ( Read(..), get, lift, (+++) )
import Text.ParserCombinators.ReadP ( char, string, (<++) )

import Control.Monad       ( liftM2, guard)
import Control.Applicative ( (<$>) )

import HyLoRes.Util ( compareUsing, showListWith )

import HyLoRes.Formula ( Formula, At, Box, Opaque,
                         NomSym, PropSym, RelSym,
                         onSubf, opaque, containsNom, specialize )

import HyLoRes.Formula.NF ( AtFormulaNF, nf, fromNF )

import HyLoRes.Clause ( Clause(..) )
import HyLoRes.Clause.BasicClause ( BasicClause,
                                    unsafeDelete, fromList, singletonClause )

import HyLoRes.Clause.SelFunction ( SelFunc, isSelectable, nil )

import HyLo.Signature ( HasSignature(..) )
import qualified HyLo.Signature as Sig

import HyLo.Model     ( ModelsRel(..), Model )

import HyLoRes.Formula.TypeLevel ( Specializable(..), Spec(..) )

data FullClause dist = FullClause {
                           clauseId       :: ClauseId,
                           distFormula    :: Formula dist,
                           wasSelected    :: Bool,
                           restOfClause   :: BasicClause,
                           toBasicClause  :: BasicClause
                       }

newtype ClauseId = ClauseId Int deriving(Eq, Ord, Num, Enum, Arbitrary)

instance Specializable FullClause where
  specialize cl =
    case specialize (distFormula cl) of
        AtTop     f' -> AtTop     cl{distFormula = f'}
        AtProp    f' -> AtProp    cl{distFormula = f'}
        AtNom     f' -> AtNom     cl{distFormula = f'}
        --
        AtNegTop  f' -> AtNegTop  cl{distFormula = f'}
        AtNegProp f' -> AtNegProp cl{distFormula = f'}
        AtNegNom  f' -> AtNegNom  cl{distFormula = f'}
        --
        AtDisj    f' -> AtDisj    cl{distFormula = f'}
        AtConj    f' -> AtConj    cl{distFormula = f'}
        --
        AtDiamNom f' -> AtDiamNom cl{distFormula = f'}
        AtDiamF   f' -> AtDiamF   cl{distFormula = f'}
        AtBoxF    f' -> AtBoxF    cl{distFormula = f'}
        --
        AtDownF   f' -> AtDownF   cl{distFormula = f'}

instance Show ClauseId where
    showsPrec _ (ClauseId i) = showChar 'C' . shows i

instance Read ClauseId where
    readPrec = do 'C' <- get; ClauseId <$> readPrec

instance Eq (FullClause dist) where
    c1 == c2 = (toBasicClause c1) == (toBasicClause c2)

instance Ord (FullClause dist) where
    compare = compareUsing toBasicClause

instance Show (FullClause (At f)) where
    showsPrec _ = showsFC . opaqueClause

showsFC :: FullClause (At Opaque) -> ShowS
showsFC  cl = shows (clauseId cl) . showString ": "
            . showListWith showF (showChar '{')
                                 sortedFrms
                                 (showChar '}')
    where showF    f = shows f . maxDecor f . if wasSelected cl
                                                then selDecor f
                                                else id
          maxDecor f = if f == max_f then showChar '+' else id
          selDecor f = if (fromNF f) == distFormula cl then showChar '*' else id
          max_f      = last sortedFrms
          sortedFrms = sort $ toFormulaList cl

instance Read (FullClause (At Opaque)) where
    readPrec =
        do clId <- readPrec
           lift (string ": ")
           '{' <- get
           deco_fs <- sepBy1 decoForm (lift $ string ", ")
           --
           (dist,wasSel):_ <- return $ [(f,True)  | (f,_,True) <- deco_fs] ++
                                       [(f,False) | (f,True,_) <- deco_fs]
           --
           '}' <- get
           --
           let res = FullClause{
                       clauseId       = clId,
                       distFormula    = dist,
                       wasSelected    = wasSel,
                       restOfClause   = unsafeDelete (distFormula   res)
                                                     (toBasicClause res),
                       toBasicClause  = fromList $ [f | (f,_,_) <- deco_fs]
                     }
           return res
      --
      where sepBy1 p sep = liftM2 (:) p (many (sep >> p))
            many   p     = return [] +++ many1 p
            many1  p     = liftM2 (:) p (many p)
            --
            decoForm = do f <- readPrec
                          isMax <- lift $ (do char '+'; return True) <++
                                          (return False)
                          isSel <- lift $ (do char '*'; return True) <++
                                          (return False)
                          return (f, isMax, isSel)


instance Clause (FullClause dist) where
    isEmpty          = isEmpty . toBasicClause
    size             = size . toBasicClause

    contains         = contains . toBasicClause
    c `subset` c'    = (toBasicClause c) `subset` (toBasicClause c')
    c `subsetEq` c'  = (toBasicClause c) `subsetEq` (toBasicClause c')

    toFormulaList    = toFormulaList . toBasicClause

instance HasSignature (FullClause f) where
    type NomsOf  (FullClause f) = NomSym
    type PropsOf (FullClause f) = PropSym
    type RelsOf  (FullClause f) = RelSym
    getSignature = getSignature . toBasicClause

instance Ord w
      => ModelsRel (Model w NomSym PropSym RelSym)
                   (FullClause f) NomSym PropSym RelSym where
    m |= cl = m |= toBasicClause cl

makeFullClause :: SelFunc -> ClauseId -> BasicClause -> FullClause (At Opaque)
makeFullClause sf clId cl = FullClause {
                               clauseId       = clId,
                               distFormula    = dist_f,
                               wasSelected    = isJust selected,
                               restOfClause   = unsafeDelete dist_f cl,
                               toBasicClause  = cl
                            }
    where (max_f, selected) = selectFormula sf cl
          dist_f   = fromNF $ fromMaybe max_f selected

-- computes both the maximum formula and the selected one (of any)
selectFormula :: SelFunc -> BasicClause -> (AtFormulaNF, Maybe AtFormulaNF)
selectFormula selFun cl = (last ordList, selFun $ filter isSelectable ordList)
    where ordList = sort $ toFormulaList cl

selectedFormula :: FullClause (At dist) -> Maybe AtFormulaNF
selectedFormula cl = do guard (wasSelected cl); return (nf . distFormula $ cl)

opaqueClause :: FullClause (At f) -> FullClause (At Opaque)
opaqueClause cl = cl{distFormula = onSubf opaque (distFormula cl)}

splitAtDist :: FullClause t -> (Formula t, BasicClause)
splitAtDist cl = (distFormula cl, restOfClause cl)

occursNom :: NomSym -> FullClause f -> Bool
occursNom n = any (containsNom n . fromNF) . toFormulaList

-----------------------------------------------------
-- QuickCheck stuff
-----------------------------------------------------

instance Arbitrary (FullClause (At Opaque)) where
    arbitrary =
        do aBasicClause <- arbitrary
           clId         <- arbitrary
           raw_idx      <- arbitrary
           sf           <- elements [
                                     nil,
                                     \fs -> do guard (not . null $ fs)
                                               let idx = raw_idx `mod` length fs
                                               return $ fs !! idx
                                    ]
           if not . isEmpty $ aBasicClause
             then return $ makeFullClause sf clId aBasicClause
             else sized $ \s ->
               if s > 0
                 then arbitrary
                 else do f      <- arbitrary
                         let _  = f :: Formula (At (Box Opaque))
                         let f' = onSubf opaque f
                         return $ makeFullClause sf clId (singletonClause f')
    --
    coarbitrary = coarbitrary . toFormulaList

prop_read_ClauseId :: ClauseId -> Bool
prop_read_ClauseId cId = cId == (read . show $ cId)

prop_read_FullClause :: FullClause (At Opaque) -> Bool
prop_read_FullClause cl = cl == (read . show $ cl)

prop_selIsSelectable :: FullClause (At Opaque) -> Bool
prop_selIsSelectable cl = fromMaybe True (isSelectable <$> selectedFormula cl)

unit_tests :: UnitTest
unit_tests = [
    ("read/show - ClauseId",           runTest prop_read_ClauseId),
    ("read/show - FullClause",         runTest prop_read_FullClause),
    ("selected formula is selectable", runTest prop_selIsSelectable)
  ]
