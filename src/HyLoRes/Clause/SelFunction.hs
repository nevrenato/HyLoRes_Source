----------------------------------------------------
--                                                --
-- HyLoRes.Clause.SelFunctions:                   --
-- Selection functions and selection functions    --
-- generators                                     --
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

module HyLoRes.Clause.SelFunction(
  SelFunc,
  nil,         -- nil selection function
  firstMatch,  -- makes a selection function given some boolean criteria

  isSelectable,

  makeClass, minInClass, minLevelInClass,

  SelFuncString, fromSelFuncString
)

where

import Data.List( find, sortBy )
import Data.Maybe( listToMaybe )

import HyLoRes.Formula.TypeLevel ( Spec(..) )

import HyLoRes.Formula( level, label, subf, specialize )

import HyLoRes.Formula.NF ( AtFormulaNF, fromNF )

{-
A selection function must pick a formula from a list of
(ascending), eligible, at-formulas
-}
type SelFunc = [AtFormulaNF] -> Maybe AtFormulaNF

isSelectable :: AtFormulaNF -> Bool
isSelectable f = case (specialize . fromNF) f of
                     AtNegNom{}  -> True
                     AtNegProp{} -> True
                     AtConj{}    -> True
                     AtDisj{}    -> True
                     AtDiamF{}   -> True
                     AtBoxF{}    -> True
                     AtDownF{}   -> True
                     _           -> False

nil :: SelFunc
nil = const Nothing

firstMatch :: (AtFormulaNF -> Bool) -> SelFunc
firstMatch = find


type SelFuncString = String


{- Given:

  - a list of boolean functions l

  returns a function that returns true whenever any of the
  functions in l return true
-}
makeClass :: [ (AtFormulaNF -> Bool) ] -> AtFormulaNF -> Bool
makeClass l f = any ($ f) l

{- Given:

  - a list l of boolean functions

  returns a selection function such that, if it selects a formula f of
  a clause c, that means that, for some integer n:

  1. f is the smallest formula that satisfies the n-th function of l
  2. no formula in c satisfies the m-th function of l, for m < n
-}
minInClass:: [ AtFormulaNF -> Bool ] -> SelFunc
minInClass l fs = listToMaybe [f | p <- l, f <- fs, p f]


{- Given:

  - a list l of boolean functions

  returns a selection function such that, if it selects a formula f of
  a clause c, that means that, for some integer n:

  1. f is the smallest formula in the lowest level (i.e. the level of the
     prefix is closest to 0) that satisfies the n-th function of l
  2. no formula in c satisfies the m-th function of l, for m < n
-}
minLevelInClass:: [ AtFormulaNF -> Bool ] -> SelFunc
minLevelInClass l fs = listToMaybe $ sortBy minLevelFirst [f | p <- l,
                                                               f <- fs,
                                                               p f]
    where minLevelFirst  a b = minLevelFirstF (fromNF a) (fromNF b)
          minLevelFirstF a b = case compare (labelLevel $ a) (labelLevel $ b) of
                                 EQ  -> compare (subf a) (subf b)
                                 neq -> neq
          labelLevel         = level . label

{- Given:
  - a string that describes how to build a selection function
    using minInClass or minLevelInClass

  returns an appropiate selection function.
-}
fromSelFuncString :: SelFuncString -> SelFunc
fromSelFuncString ('L':xs) = buildUsing minLevelInClass xs
fromSelFuncString  xs      = buildUsing minInClass      xs

buildUsing :: ([AtFormulaNF -> Bool] -> SelFunc) -> SelFuncString -> SelFunc
buildUsing mkFun = mkFun . map (\f -> f . fromNF) . map c2f
    where c2f 'n' f = case specialize f of
                          { AtNegNom{} -> True; AtNegProp{} -> True; _ -> False }
          c2f 'a' f = case specialize f of { AtConj{} -> True; _ -> False }
          c2f 'o' f = case specialize f of { AtDisj{} -> True; _ -> False }
          c2f 'd' f = case specialize f of { AtDiamF{} -> True; _ -> False }
          c2f 'b' f = case specialize f of { AtBoxF{} -> True; _ -> False }
          c2f _   _ = error "Error in string specifying selection function.\n"
