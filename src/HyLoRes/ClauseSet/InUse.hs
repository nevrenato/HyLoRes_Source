-- Need this for ghc >= 7
{-# LANGUAGE NoMonoLocalBinds #-}
----------------------------------------------------
--                                                --
-- HyLoRes.ClauseSet.InUse:                       --
-- A set of FullClauses classified by the         --
-- family of the distinguished formula            --
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
module HyLoRes.ClauseSet.InUse(
    -- types
    InUseClauseSet,

    -- constructors
    newSet,

    -- manipulators
    add, remove,

    -- observers
    allClauses, clausesByNom, clauses, keys,
    allClausesByFamily, allClausesIdx, allClausesOpaquedIdx,

    -- indexes
    unitEqIdx, nonUnitEqIdx, atNegNomIdx,
    atPropIdx,   atNegPropIdx,
    atDiaNomIdx, atDiaNomRevIdx,
    atBoxFIdx,

    -- show
    showPretty,

    -- unit tests
    unit_tests
)

where

import Test.QuickCheck          ( Arbitrary(..), sized, resize )
import HyLo.Test                ( UnitTest, runTest )
import Control.Monad            ( replicateM )

import Data.Maybe ( fromMaybe )
import Data.List  ( sort, nub, foldl' )

import Data.Map ( Map )
import qualified Data.Map as Map

import Text.Read                       ( Read(..) )
import Text.ParserCombinators.ReadP    ( string, skipSpaces )
import Text.ParserCombinators.ReadPrec ( lift )

import HyLoRes.Formula ( NomSym, PropSym, RelSym,
                         At, Nom, Prop, Neg, Box, Diam, Opaque,
                         label, relSym, flatten, subf, specialize )
import HyLoRes.Formula.TypeLevel ( Spec(..) )

import HyLo.Signature  ( hasInv )

import HyLoRes.Util          ( filterFirst )
import HyLoRes.Util.Classify ( classifyBy )

import HyLoRes.Clause            ( size )
import HyLoRes.Clause.FullClause ( FullClause, clauseId, distFormula,
                                   opaqueClause,
                                   specialize )
import qualified HyLoRes.Clause.FullClause as FC


data InUseClauseSet = IU {unitEqIdx      :: InUseIdx (At Nom)          NomSym,
                          nonUnitEqIdx   :: InUseIdx (At Nom)          NomSym,
-- reducing type safety. Need to comment, because of ghc >= 7.
-- The next line replaces the commented 
--			  atNegNomIdx    :: InUseIdx (At (Neg Nom))    (Neg NomSym),                         
			  atNegNomIdx    :: InUseIdx (At (Neg Nom))    NomSym,
			  atPropIdx      :: InUseIdx (At Prop)         PropSym,
                          atNegPropIdx   :: InUseIdx (At (Neg Prop))   PropSym,
                          atBoxFIdx      :: InUseIdx (At (Box Opaque)) RelSym,
                          atDiaNomIdx    :: InUseIdx (At (Diam Nom))   RelSym,
                          atDiaNomRevIdx :: InUseIdx (At (Diam Nom))   RelSym}

data InUseIdx f k =
    InUseIdx {asMap     :: Map NomSym (Map k [FullClause f]),
              nomPicker :: FullClause f -> NomSym,
              keyPicker :: FullClause f -> k}

mkIdx :: (FullClause f -> NomSym) -> (FullClause f -> k) -> InUseIdx f k
mkIdx f g = InUseIdx {asMap = Map.empty, nomPicker = f, keyPicker = g}

newSet :: InUseClauseSet
newSet =
    IU{unitEqIdx      = mkIdx (fst  . flatten . distF) (snd  . flatten . distF),
       nonUnitEqIdx   = mkIdx (fst  . flatten . distF) (snd  . flatten . distF),
       atNegNomIdx    = mkIdx (fst  . flatten . distF) (snd  . flatten . distF),
       atPropIdx      = mkIdx (fst  . flatten . distF) (snd  . flatten . distF),
       atNegPropIdx   = mkIdx (fst  . flatten . distF) (snd  . flatten . distF),
       atDiaNomIdx    = mkIdx (fst3 . flatten . distF) (snd3 . flatten . distF),
       atDiaNomRevIdx = mkIdx (thd3 . flatten . distF) (snd3 . flatten . distF),
       atBoxFIdx      = mkIdx (label . distF) (relSym . subf  . distF)}
    where fst3 (x,_,_) = x
          snd3 (_,x,_) = x
          thd3 (_,_,x) = x
          distF        = distFormula

addI :: Ord k => FullClause f -> InUseIdx f k -> InUseIdx f k
addI cl idx = idx{asMap = addToMap (nomPicker idx cl)
                                   (keyPicker idx)
                                   (asMap idx)}
    where addToMap i f = Map.insertWith (\_ -> classifyBy f cl)
                                        i
                                        (Map.singleton (f cl) [cl])

add :: FullClause (At f) -> InUseClauseSet -> InUseClauseSet
add cl iu =
  case specialize cl of
      AtNom     c -> if size c == 1
                     then iu{unitEqIdx      = addI c (unitEqIdx      iu)}
                     else iu{nonUnitEqIdx   = addI c (nonUnitEqIdx   iu)}
      AtNegNom  c -> iu{atNegNomIdx    = addI c (atNegNomIdx    iu)}
      AtProp    c -> iu{atPropIdx      = addI c (atPropIdx      iu)}
      AtNegProp c -> iu{atNegPropIdx   = addI c (atNegPropIdx   iu)}
      AtDiamNom c -> if hasInv (relSym . subf $ distFormula c)
                     then iu{atDiaNomIdx    = addI c (atDiaNomIdx    iu),
                             atDiaNomRevIdx = addI c (atDiaNomRevIdx iu)}
                     else iu{atDiaNomIdx    = addI c (atDiaNomIdx    iu)}
      AtBoxF    c -> iu{atBoxFIdx      = addI c (atBoxFIdx      iu)}
      _           -> error $ "InUse.add: can't store " ++ show cl

removeI :: Ord k => FullClause f ->  InUseIdx f k -> InUseIdx f k
removeI cl idx = idx{asMap = removeFromMap (nomPicker idx cl)
                                           (keyPicker idx)
                                           (asMap idx)}
    where removeFromMap nom f = Map.adjust (removeClause (f cl)) nom
          removeClause        = Map.adjust (filterFirst ((clId ==) . clauseId))
          clId                = clauseId cl

remove :: FullClause (At f) -> InUseClauseSet -> InUseClauseSet
remove cl iu =
    case specialize cl of
        AtNom c     -> if size c == 1
                       then  iu{unitEqIdx     = removeI c (unitEqIdx      iu)}
                       else  iu{nonUnitEqIdx  = removeI c (nonUnitEqIdx   iu)}
        AtNegNom c  -> iu{atNegNomIdx    = removeI c (atNegNomIdx    iu)}
        AtProp c    -> iu{atPropIdx      = removeI c (atPropIdx      iu)}
        AtNegProp c -> iu{atNegPropIdx   = removeI c (atNegPropIdx   iu)}
        AtDiamNom c -> if hasInv (relSym . subf $ distFormula c)
                       then iu{atDiaNomIdx    = removeI c (atDiaNomIdx    iu),
                               atDiaNomRevIdx = removeI c (atDiaNomRevIdx iu)}
                       else iu{atDiaNomIdx    = removeI c (atDiaNomIdx    iu)}
        AtBoxF c    -> iu{atBoxFIdx      = removeI c (atBoxFIdx      iu)}
        _           -> iu


allClauses :: InUseClauseSet -> [FullClause (At Opaque)]
allClauses iu =  concat [allClausesOpaquedIdx . atPropIdx    $ iu,
                         allClausesOpaquedIdx . atNegPropIdx $ iu,
                         allClausesOpaquedIdx . unitEqIdx    $ iu,
                         allClausesOpaquedIdx . nonUnitEqIdx $ iu,
                         allClausesOpaquedIdx . atNegNomIdx  $ iu,
                         allClausesOpaquedIdx . atBoxFIdx    $ iu,
                         allClausesOpaquedIdx . atDiaNomIdx  $ iu]

allClausesOpaquedIdx :: InUseIdx (At f) k -> [FullClause (At Opaque)]
allClausesOpaquedIdx =  map opaqueClause . allClausesIdx

allClausesIdx :: InUseIdx (At f) k -> [FullClause (At f)]
allClausesIdx =  concat . concatMap Map.elems . Map.elems . asMap


clausesByNom :: NomSym -> InUseIdx f k -> [FullClause f]
clausesByNom nom = maybe [] (concat . Map.elems) . Map.lookup nom . asMap

clauses :: Ord k => NomSym -> k -> InUseIdx f k -> [FullClause f]
clauses nom k index = fromMaybe [] $ do m <- Map.lookup nom (asMap index)
                                        Map.lookup k m

allClausesByFamily :: InUseClauseSet -> [(String, [FullClause (At Opaque)])]
allClausesByFamily iu = [("AtN"   , concat[
                                     allClausesOpaquedIdx . unitEqIdx    $ iu,
                                     allClausesOpaquedIdx . nonUnitEqIdx $ iu
                                    ]),
                         ("At!N"  , allClausesOpaquedIdx . atNegNomIdx  $ iu),
                         ("AtP"   , allClausesOpaquedIdx . atPropIdx    $ iu),
                         ("At!P"  , allClausesOpaquedIdx . atNegPropIdx $ iu),
                         ("AtDiaN", allClausesOpaquedIdx . atDiaNomIdx  $ iu),
                         ("AtBoxF", allClausesOpaquedIdx . atBoxFIdx    $ iu)]

keys :: InUseIdx f k -> [(NomSym, k)]
keys  idx = [(i,k) | (i,m) <- Map.toList (asMap idx), k <- Map.keys m]

showPretty :: InUseClauseSet -> String
showPretty iu = unlines . concat $ [["InUse: {"],
                                    map (uncurry showF) (allClausesByFamily iu),
                                    ["}"]
                                   ]
    where showF _  []    = ""
          showF f [c]    = concat  ["    ", f, ": { ", show c, "}\n"]
          showF f (c:cs) = unlines . concat $ [
                              [concat ["    ", f, ": { ", show c]],
                                       map ((indent ++) . show) cs,
                                       ["    }"]
                                    ]
          indent = "            "

-- ----------------------
-- QuickCheck stuff
-- ----------------------

instance Arbitrary InUseClauseSet where
    arbitrary = sized $ \n ->
                  do cs <- replicateM n (simpleClause (n `div` 2))
                     return $ fromClauseList (filter isSimple cs)
        where simpleClause n = do c <- resize n arbitrary
                                  if isSimple c
                                    then (return c)
                                    else simpleClause n
              isSimple c = case specialize c of
                               AtNom{}     -> True
                               AtNegNom{}  -> True
                               AtProp{}    -> True
                               AtNegProp{} -> True
                               AtDiamNom{} -> True
                               AtBoxF{}    -> True
                               AtDownF{}   -> False
                               _           -> False

    coarbitrary = coarbitrary . allClauses

fromClauseList :: [FullClause (At Opaque)] -> InUseClauseSet
fromClauseList = foldl' (flip add) newSet

instance Eq InUseClauseSet where
    iu == iu' = map sort (toList iu) == map sort (toList iu')
        where toList x = [allClausesOpaquedIdx $ unitEqIdx      x,
                          allClausesOpaquedIdx $ nonUnitEqIdx   x,
                          allClausesOpaquedIdx $ atNegNomIdx    x,
                          allClausesOpaquedIdx $ atPropIdx      x,
                          allClausesOpaquedIdx $ atNegPropIdx   x,
                          allClausesOpaquedIdx $ atBoxFIdx      x,
                          allClausesOpaquedIdx $ atDiaNomIdx    x,
                          allClausesOpaquedIdx $ atDiaNomRevIdx x]

instance Show InUseClauseSet where
    show iu = unlines [
                "IU {",
                "  unitEqIdx      = " ++ showIdx unitEqIdx      iu,
                "  nonUnitEqIdx   = " ++ showIdx nonUnitEqIdx   iu,
                "  atNegNomIdx    = " ++ showIdx atNegNomIdx    iu,
                "  atPropIdx      = " ++ showIdx atPropIdx      iu,
                "  atNegPropIdx   = " ++ showIdx atNegPropIdx   iu,
                "  atBoxFIdx      = " ++ showIdx atBoxFIdx      iu,
                "  atDiaNomIdx    = " ++ showIdx atDiaNomIdx    iu,
                "  atDiaNomRevIdx = " ++ showIdx atDiaNomRevIdx iu,
                "}"
               ]
              where showIdx idx = show . allClausesIdx . idx

instance Read InUseClauseSet where
    readPrec =
        do str "IU {"
           unit_eqs     <- readIdx "unitEqIdx"
           non_unit_eqs <- readIdx "nonUnitEqIdx"
           neqs         <- readIdx "atNegNomIdx"
           props        <- readIdx "atPropIdx"
           negProps     <- readIdx "atNegPropIdx"
           boxes        <- readIdx "atBoxFIdx"
           rels         <- readIdx "atDiaNomIdx"
           relsInv      <- readIdx "atDiaNomRevIdx"
           str "}"
           return . fromClauseList $ concat [unit_eqs,
                                             non_unit_eqs,
                                             neqs,
                                             props,
                                             negProps,
                                             boxes,
                                             nub (rels ++ relsInv)]
      where readIdx s = do str s; str "="; r <- readPrec; return r
            str     s = lift (skipSpaces >> string s >> skipSpaces)

prop_readShow :: InUseClauseSet -> Bool
prop_readShow iu = iu == (read . show $ iu)

prop_unitEqs :: InUseClauseSet -> Bool
prop_unitEqs iu = all (\c -> size c == 1) (allClausesIdx $ unitEqIdx    iu) &&
                  all (\c -> size c  > 1) (allClausesIdx $ nonUnitEqIdx iu)

prop_relsAndInvs :: InUseClauseSet -> Bool
prop_relsAndInvs iu = all (match atDiaNomRevIdx) (cls atDiaNomIdx) &&
                      all (match atDiaNomIdx)    (cls atDiaNomRevIdx)
    where match idx c
            | hasInv (relSym . subf $ distFormula c) = c `elem` (cls idx)
            | otherwise                        = not $ c `elem` (cls idx)
          cls idx = allClausesIdx (idx iu)

unit_tests :: UnitTest
unit_tests = [
    ("read/show - InUseClauseSet",  runTest prop_readShow),
    ("unit eqs where they belong",  runTest prop_unitEqs),
    ("atDiaNomRevIdx has inverses", runTest prop_relsAndInvs)
  ]
