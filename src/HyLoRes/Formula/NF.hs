module HyLoRes.Formula.NF( AtFormulaNF, fromNF, nf,
                           --
                           unit_tests )

where

import Test.QuickCheck ( Arbitrary(..), Gen )
import HyLo.Test       ( UnitTest, runTest )

import Text.Read ( Read(readPrec) )

import HyLo.Signature ( HasSignature (..) )
import HyLo.Model     ( ModelsRel(..), Model )

import HyLoRes.Formula.TypeLevel ( Spec(..) )

import HyLoRes.Formula ( Formula, At, Nom, Neg, Opaque,
                         NomSym, PropSym, RelSym,
                         onSubf, opaque, at, nom , neg, flatten,
                         specialize )

import Data.Hash ( Hashable )

newtype AtFormulaNF = NF{fromNF :: Formula (At Opaque)}
                      deriving (Eq, Ord, Hashable)

nf :: Formula (At f) -> AtFormulaNF
nf at_f = case specialize at_f of
              AtTop f     -> (NF . mkAtOpaque) f
              AtProp f    -> (NF . mkAtOpaque) f
              AtNom f     -> (NF . mkAtOpaque . normalizeEq) f
              --
              AtNegTop f  -> (NF . mkAtOpaque) f
              AtNegProp f -> (NF . mkAtOpaque) f
              AtNegNom f  -> (NF . mkAtOpaque . normalizeNeq) f
              --
              AtDisj f    -> (NF . mkAtOpaque) f
              AtConj f    -> (NF . mkAtOpaque) f
              --
              AtDiamNom f -> (NF . mkAtOpaque) f
              AtDiamF f   -> (NF . mkAtOpaque) f
              AtBoxF f    -> (NF . mkAtOpaque) f
              --
              AtDownF f   -> (NF . mkAtOpaque) f

mkAtOpaque :: Formula (At f) -> Formula (At Opaque)
mkAtOpaque = onSubf opaque

normalizeEq :: Formula (At Nom) -> Formula (At Nom)
normalizeEq f = if i > j then f else at j (nom i)
    where (i,j) = flatten f

normalizeNeq :: Formula (At (Neg Nom)) -> Formula (At (Neg Nom))
normalizeNeq f = if i > j then f else at j (neg $ nom i)
    where (i,j) = flatten f


instance Show AtFormulaNF where
    show = show . fromNF

instance Read AtFormulaNF where
    readPrec = do f <- readPrec; return (NF f)

instance HasSignature AtFormulaNF where
    type NomsOf  AtFormulaNF = NomSym
    type PropsOf AtFormulaNF = PropSym
    type RelsOf  AtFormulaNF = RelSym
    getSignature (NF f) = getSignature f

instance Ord w
      => ModelsRel (Model w NomSym PropSym RelSym)
                   AtFormulaNF NomSym PropSym RelSym where
    m |= (NF f) = m |= f

-- ---------------------------
-- QuickCheck stuff
-- ---------------------------

instance Arbitrary AtFormulaNF where
    arbitrary = do f <- arbitrary :: Gen (Formula (At Opaque))
                   return $ nf f
    coarbitrary = coarbitrary . fromNF

prop_orient_eq :: NomSym -> NomSym -> Bool
prop_orient_eq i j = case specialize f of
                         AtNom f' -> (uncurry (>=) . flatten) f'
                         _        -> undefined
                    where f = fromNF . nf $ at i (nom j)

prop_orient_neq :: NomSym -> NomSym -> Bool
prop_orient_neq i j = case specialize f of
                          AtNegNom f' -> (uncurry (>=) . flatten) f'
                          _           -> undefined
                      where f = fromNF . nf $ at i (neg $ nom j)

unit_tests :: UnitTest
unit_tests = [
    ("eqs are oriented",  runTest prop_orient_eq),
    ("neqs are oriented", runTest prop_orient_neq)
  ]
