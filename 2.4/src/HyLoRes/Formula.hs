----------------------------------------------------
--                                                --
-- HyLoRes.Formula:                               --
-- Formula data type                              --
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
module HyLoRes.Formula(

  -- Signature
  Signature, NomSym, RelSym(..), PropSym(..),

  -- nominals
  NomId, spyU, evalPoint, inputNom, toNom, var, isVar,
  level, isSkolemNom, isInputNom, onInvToNom, nomId, varId,

  -- relation symbols
  invRel,

  -- Formula types
  Formula, AtFormula,
  Top, Prop, Nom, Neg, Conj, Disj, Diam, Box, At, Down, Opaque,

  -- formula construction
  nnfAtFormula,
  top, prop, nom, at, down, diam, box, neg, takeConj, takeDisj,
  opaque, asAtOpaque,
  replaceNom, killNom, instanceFreeVar,

  -- formula manipulation
  label, boundVar, subf, onSubf, subfs, relSym, symbol, unNNF, containsNom,

  flatten,

  specialize,

  -- Other
  HashOrd(..), CachedHash, cacheHash, fromCachedHash,

  -- Unit tests
  unit_tests
)

where

import Test.QuickCheck       ( Arbitrary(..), Gen, Property,
                               forAll, oneof, variant, sized, resize )
import Test.QuickCheck.Utils ( isTotalOrder )
import HyLo.Test             ( UnitTest, runTest )

import Control.Monad ( liftM )

import Data.List  ( sort, foldl1' )
import Data.Maybe ( mapMaybe, fromMaybe )

import Data.Set ( Set )
import qualified Data.Set as Set

import Data.Hash

import HyLoRes.Util.Ordering ( metap_trichotomy,
                               metap_irreflexive,
                               metap_antisymmetric,
                               metap_transitive )

import qualified HyLo.Formula as F

import HyLoRes.Formula.Internal hiding ( nnfAtFormula, unit_tests )
import qualified HyLoRes.Formula.Internal as I

import HyLoRes.Formula.TypeLevel ( Top, Prop, Nom,
                                   Neg, Disj, Conj,
                                   Diam, Box, At, Down,
                                   Opaque,
                                   Specializable(..), Spec(..) )

import qualified HyLo.Signature as S
import HyLo.Signature ( HasSignature(..), nomSymbols, merge, IsRelSym(..) )

import Text.Read ( Read(..) )
import qualified Text.ParserCombinators.ReadPrec as P ( lift )
import           Text.ParserCombinators.ReadPrec      ( get, choice )
import           Text.ParserCombinators.ReadP         ( string )

-- =============================== Signature ============================ --
--       (this ought to be in a separate module, but ghc's
--        support for mutually recursive modules is quite poor)

type Signature = S.Signature NomSym PropSym RelSym

newtype PropSym = P Int deriving (Eq, Ord, Arbitrary)

instance Show PropSym where
    show (P p) = 'P' : show p

instance Read PropSym where
    readPrec = do 'P' <- get; P `liftM` readPrec

instance Hashable PropSym where
    hash (P p) = hash p

-- the order of the constructors guarantee
-- Univ < Rel _ < RelInv _
data RelSym = Univ | Rel Int | RelInv Int deriving (Eq, Ord)

instance Show RelSym where
    show (Rel r)    = 'R' : show r
    show (RelInv r) = '-' : show (Rel r)
    show  Univ      = "U"

instance Read RelSym where
    readPrec = choice [do 'R' <- get; Rel `liftM` readPrec,
                       do '-' <- get; Rel r <- readPrec; return $ RelInv r,
                       do 'U' <- get; return Univ]

instance IsRelSym RelSym where
    invRel (Rel r)    = Just (RelInv r)
    invRel (RelInv r) = Just (Rel r)
    invRel Univ       = Nothing


instance Hashable RelSym where
    hash (Rel r)    = hash 'R' `combine` hash r
    hash (RelInv r) = hash 'r' `combine` hash r
    hash Univ       = hash 'U'

{- Nominals are split in "Input-Nominals" (N_i) and "Calculus-Nominals" (N_c) -}

type    Level  = Int
newtype NomId  = NomId Int deriving(Eq, Ord, Show, Read,
                                    Enum, Num, Real, Integral,
                                    Hashable, Arbitrary)

data NomSym = NspyU
            | Neval
            | Ni NomId
            | Nc Level (Formula (At (Diam Opaque)))
            | X  NomId
             deriving (Eq)

instance Ord NomSym where
    -- In order to guarantee termination, we must check that deeper nominals
    -- are always the greatest in the order. On the other hand, if we have
    -- two nominals on the same level, the greatest must be the one whose
    -- associated formula is the greatest (this is to guarantee i > j iff
    -- tonom(@_i<r>A) > tonom(@_j<r>A))
    -- NspyU and Neval are given a low precedence with no real good reason
    compare  NspyU      NspyU     = EQ
    compare  NspyU      _         = LT
    --
    compare  Neval      Neval     = EQ
    compare  Neval      NspyU     = GT
    compare  Neval      _         = LT
    --
    compare (Ni id1)   (Ni id2)   = compare id1 id2
    compare (Ni _)     (Nc _ _)   = LT
    compare (Ni _)     (X _)      = LT
    compare (Ni _)      _         = GT
    --
    compare (Nc l1 f1) (Nc l2 f2) = case compare l1 l2 of
                                        EQ  -> compare f1 f2
                                        neq -> neq
    compare (Nc _ _)   (X _)      = LT
    compare (Nc _ _)    _         = GT
    --
    compare (X x)      (X y)      = compare x y
    compare (X _)       _         = GT

instance Show NomSym where
    showsPrec _  NspyU          = showString "N_spy"
    showsPrec _  Neval          = showString "N_eval"
    showsPrec _ (Ni (NomId i))  = showChar 'N' . shows i
    showsPrec _ (Nc l f)        = showString "N_{" . shows l . showString ", " .
                                  shows f . showChar '}'
    showsPrec _ (X  (NomId x))  = showChar 'X' . shows x

instance Read NomSym where
    readPrec = choice [
                   do P.lift (string "N_spy"); return NspyU,
                   --
                   do P.lift (string "N_eval"); return Neval,
                   --
                   do 'N' <- get; (Ni . NomId) `liftM` readPrec,
                   --
                   do P.lift (string "N_{")
                      l   <- readPrec; P.lift (string ", ")
                      f   <- asAtDiamF =<< readPrec
                      '}' <- get
                      return $ Nc l f,
                   --
                   do 'X' <- get; (X . NomId) `liftM` readPrec
               ]

instance Hashable NomSym where
    hash NspyU    = hash 's'
    hash Neval    = hash 'e'
    hash (Ni i)   = hash 'i' `combine` hash i
    hash (Nc _ f) = hash 'c' `combine` hash f
    hash (X i)    = hash 'x' `combine` hash i


asAtDiamF :: Monad m => Formula Opaque -> m (Formula (At (Diam Opaque)))
asAtDiamF (Opaque   (At _ _ (Diam _ _ Nom{}))) = fail "Is a rel"
asAtDiamF (Opaque f@(At _ _  Diam{}))          = return$onSubf (onSubf opaque) f
asAtDiamF  _                                   = fail "Not an AtNomDiam formula"


spyU :: NomSym
spyU = NspyU

evalPoint :: NomSym
evalPoint = Neval

inputNom :: NomId -> NomSym
inputNom = Ni

var :: NomId -> NomSym
var =  X

isSkolemNom :: NomSym -> Bool
isSkolemNom (Nc _ _) = True
isSkolemNom  _      = False

isInputNom :: NomSym -> Bool
isInputNom (Ni _) = True
isInputNom _      = False

nomId :: NomSym -> Maybe NomId
nomId (Ni i) = Just i
nomId _      = Nothing

isVar :: NomSym -> Bool
isVar (X _) = True
isVar _     = False

varId :: NomSym -> Maybe NomId
varId (X x ) = Just x
varId _      = Nothing

level :: NomSym -> Level
level NspyU    = 0
level Neval    = 0
level (Ni _)   = 0
level (Nc l _) = l
level (X _)    = 0

toNom :: Formula (At (Diam f)) -> NomSym
toNom f = Nc (succ . level . label $ f) (onSubf (onSubf opaque) f)

onInvToNom :: NomSym -> (forall f . Formula (At (Diam f)) -> r) -> Maybe r
onInvToNom (Nc _ f) g = Just $ g f
onInvToNom _        _ = Nothing


-- ============================== Formula ================================== --

type Formula f = Form NomSym PropSym RelSym Cached f

data Cached = Cached {
                _phi       :: Int,
                _hash      :: Hash,
                _nomHashes :: Set Hash
              }

instance Attrib Cached NomSym PropSym RelSym where
    computeAttrib f = Cached {
                        _phi       = computePhi  f,
                        _hash      = computeHash f,
                        _nomHashes = computeNomHashes f
                      }

nnfAtFormula :: F.Formula NomSym PropSym RelSym -> Formula (At Opaque)
nnfAtFormula = I.nnfAtFormula evalPoint

type AtFormula = Formula (At Opaque)

asAtOpaque :: Formula (At f) -> AtFormula
asAtOpaque = onSubf opaque

instance Eq (Formula f) where
    f == g = (hash f == hash g) && (eqUnNNF f g)

instance HasSignature (Formula f) where
    type NomsOf  (Formula f) = NomSym
    type PropsOf (Formula f) = PropSym
    type RelsOf  (Formula f) = RelSym
    getSignature f = foldl1' merge (sig_f:sig_sk_noms)
        where sig_f       = getSignature $ unNNF f
              sig_sk_noms = mapMaybe skNomSig . Set.toList . nomSymbols $ sig_f
              skNomSig (Nc _ f') = Just (getSignature f')
              skNomSig _         = Nothing

killNom :: NomSym -> NomSym -> Formula f -> Formula f
killNom i i' f = mapSig killIt id id f
    where killIt  j | j == i = i'
          killIt (Nc _ f')   = toNom (killNom i i' f')
          killIt  j          = j


-- =============== Public constructors for formulas ================= --

-- disjunctions and conjunctions are sorted to obtain a normal representation

takeDisj :: [Formula f] -> Formula Disj
takeDisj f@(_:_:_) = disj $ sort f
takeDisj _         = error "takeDisj: not enough disjuncts"

takeConj :: [Formula f] -> Formula Conj
takeConj f@(_:_:_) = conj $ sort f
takeConj _         = error "takeConj: not enough conjuncts"

-- ================== Admissible ordering ============

args :: Formula a -> [Formula Opaque]
args = nonOpaque args'
  where args' :: Formula f -> [Formula Opaque]
        args' Top{}       = []
        args' Nom{}       = []
        args' Prop{}      = []
        --
        args'   NegTop{}  = [opaque top]
        args' a@NegNom{}  = [opaque $ subf a]
        args' a@NegProp{} = [opaque $ subf a]
        --
        -- observe that when turning @_aF to a term structure,
        -- the nominal (or var) must be the second argument
        args' f@Conj{}    = map opaque (subfs f)
        args' f@Disj{}    = map opaque (subfs f)
        --
        args' f@At{}      = [opaque (subf f), opaque $ nom (label f)]
        --
        args' f@Down{}    = [opaque $ nom (boundVar f), opaque (subf f)]
        --
        args' f@Box{}     = [opaque $ subf f]
        args' f@Diam{}    = [opaque $ subf f]
        --
        args' (Opaque _)  = error "args': opaque!"

instance Ord (Formula f) where
    compare f1 f2 = compareF f1 f2

compareF :: Formula f -> Formula g -> Ordering
compareF = cmp_kbo


cmp_kbo :: Formula a -> Formula b -> Ordering
cmp_kbo f1 f2 = nonOpaque2 (\f g -> snd $ kbo f g 0) f1 f2

kbo :: Formula a -> Formula b -> Int -> (Int, Ordering)
kbo s t wb_i = case compare wb_f 0 of
                 EQ  -> case cmp_head of
                          EQ  -> (wb_f, lex_res)
                          res -> (wb_f, res)
                 res -> (wb_f, res)
    where cmp_head        = compareHead s t
          (wb_f, lex_res) = if cmp_head == EQ then
                              let (wb_s, res) = kbolex s t wb_i
                              in  (wb_s + weightHead s - weightHead t, res)
                            else
                              (wb_i + phi s - phi t,
                               error $ "lex_res shouldn't be used! ")

kbolex :: Formula a -> Formula b -> Int -> (Int, Ordering)
kbolex = nonOpaque2 kbolex'
  where
   kbolex' :: Formula a -> Formula b -> Int -> (Int, Ordering)
   kbolex'   Top{}    _      wb = (wb, EQ)
   kbolex' f@Nom{}  g@Nom{}  wb = (wb, compare (symbol f) (symbol g))
   kbolex' f@Prop{} g@Prop{} wb = (wb, compare (symbol f) (symbol g))
   --
   kbolex'   NegTop{}    _         wb = (wb, EQ)
   kbolex' f@NegNom{}  g@NegNom{}  wb = (wb,compare (negSymbol f) (negSymbol g))
   kbolex' f@NegProp{} g@NegProp{} wb = (wb,compare (negSymbol f) (negSymbol g))
   --
   kbolex' f@Conj{} g@Conj{} wb = kbolex_list (subfs f) (subfs g) wb
   kbolex' f@Disj{} g@Disj{} wb = kbolex_list (subfs f) (subfs g) wb
   --
   -- observe that when turning @_aF to a term structure,
   -- the nominal (or var) must be the second argument
   kbolex' f@At{} g@At{}   wb = case kbo (subf f) (subf g) wb of
                                  (wb',EQ) -> (wb',compare (label f) (label g))
                                  res      -> res
   --
   kbolex' f@Down{} g@Down{} wb = case kbo (subf f) (subf g) wb of
                                   (wb',EQ) -> (wb',compare (boundVar f)
                                                            (boundVar g))
                                   res      -> res
   --
   kbolex' f@Box{}  g@Box{}  wb = kbo (subf f) (subf g) wb
   kbolex' f@Diam{} g@Diam{} wb = kbo (subf f) (subf g) wb
   --
   kbolex' Opaque{} _         _ = error "kbolex': opaque l!"
   kbolex' _        Opaque{}  _ = error "kbolex': opaque r!"
   --
   kbolex' s t _ = error $ unlines ["kbolex' - non equal:",
                                    "   s = " ++ show s,
                                    "   t = " ++ show t]
   --
   kbolex_list :: [Formula a]-> [Formula b]-> Int -> (Int,Ordering)
   kbolex_list [] [] wb = (wb, EQ)
   kbolex_list (f:fs) (g:gs) wb = case kbo f g wb of
                                     (wb', EQ)  -> kbolex_list fs gs wb'
                                     (wb', res) -> (wb' + sum_phi fs
                                                        - sum_phi gs,res)
   kbolex_list _ _ _            = error "kbolex_list: wrong arity"
   --
   sum_phi :: [Formula a] -> Int
   sum_phi = sum . map phi

phi :: Formula f -> Int
phi = _phi . attrib

computePhi :: Formula f -> Int
computePhi = nonOpaque phi'
    where phi' :: Formula f -> Int
          phi' a@Top{}     = weightHead a
          phi' a@Nom{}     = weightHead a
          phi' a@Prop{}    = weightHead a
          --
          phi' a@NegTop{}  = weightHead a
          phi' a@NegNom{}  = weightHead a
          phi' a@NegProp{} = weightHead a
          --
          phi' f@Conj{}    = sum $ map phi (subfs f)
          phi' f@Disj{}    = sum $ map phi (subfs f)
          --
          phi' f@At{}      = weightHead (nom $ label f) + phi (subf f)
          --
          phi' f@Down{}    = weightHead (nom $ boundVar f) + phi (subf f)
          --
          phi' f@Box{}     = weightHead f + phi (subf f)
          phi' f@Diam{}    = weightHead f + phi (subf f)
          --
          phi' (Opaque _)  = error "phi: opaque!"

compareHead :: Formula a -> Formula b -> Ordering
compareHead = nonOpaque2 cmpHead
    where cmpHead :: Formula a -> Formula b -> Ordering
          cmpHead f@Nom{}     g@Nom{}     = compare (symbol f) (symbol g)
          cmpHead f@Prop{}    g@Prop{}    = compare (symbol f) (symbol g)
          --
          cmpHead f@NegNom{}  g@NegNom{}  = compare(negSymbol f) (negSymbol g)
          cmpHead f@NegProp{} g@NegProp{} = compare(negSymbol f) (negSymbol g)
          --
          cmpHead f@Diam{}    g@Diam{}    = compare (relSym f) (relSym g)
          cmpHead f@Box{}     g@Box{}     = compare (relSym f) (relSym g)
          --
          cmpHead f@Conj{}    g@Conj{}    = cmpLen (subfs f) (subfs g)
          cmpHead f@Disj{}    g@Disj{}    = cmpLen (subfs f) (subfs g)
          --
          cmpHead  f g = case compare (weightHead f) (weightHead g) of
                            EQ  -> compare (linear f) (linear g)
                            res -> res
          --
	  cmpLen :: [a] -> [a] -> Ordering
          cmpLen  [] [] = EQ
          cmpLen  []  _ = LT
          cmpLen  _  [] = GT
          cmpLen (_:xs) (_:ys) = cmpLen xs ys
          --
          linear :: Formula a -> Int
          linear Nom{}     = 0
          linear Top{}     = 1
          linear At{}      = 2
          linear Down{}    = 5
          linear Diam{}    = 6
          linear Box{}     = 7
          linear Prop{}    = 8
          linear Conj{}    = 9
          linear Disj{}    = 10
          linear NegNom{}  = 11
          linear NegTop{}  = 12
          linear NegProp{} = 14
          linear Opaque{}  = error "linear: opaque!"

weightHead :: Formula f -> Int
weightHead = nonOpaque weightHead'
    where {-# INLINE weightHead' #-}
          weightHead' :: Formula f -> Int
            -- all nominals weight the same, and less than the rest
          weightHead'   Nom{}     = 1
            -- @ and top are unimportant, so they weight little
          weightHead'   Top{}     = 2
          weightHead'   At{}      = 2
            -- down weights little, so we try to postpone loop
            -- inducing formulas
          weightHead'   Down{}    = 2
            --
          weightHead'   Diam{}    = 4
            -- boxes weight more than diamonds
          weightHead'   Box{}     = 5
            -- we favor @ip over @i<>j, etc
          weightHead'   Prop{}    = 30
          weightHead' f@Conj{}    = 50 + length (subfs f)
          weightHead' f@Disj{}    = 60 + length (subfs f)
            -- neg's like in @i-p, weight a lot, so we can favour resolution
            -- over other structural rules
          weightHead'   NegNom{}  = 201
          weightHead'   NegTop{}  = 202
          weightHead'   NegProp{} = 230
          weightHead'   Opaque{}  = error "weightHead': can't happen"


instance Hashable (Formula f) where
    hash = _hash . attrib

computeHash :: Formula f -> Hash
computeHash Top{}       = hash 'T'
computeHash NegTop{}    = hash 't'
computeHash f@Nom{}     = hash 'N' `combine` hash (symbol f)
computeHash f@NegNom{}  = hash 'n' `combine` hash (negSymbol f)
computeHash f@Prop{}    = hash 'P' `combine` hash (symbol f)
computeHash f@NegProp{} = hash 'p' `combine` hash (negSymbol f)
computeHash f@Conj{}    = hash '&' `combine` hash (subfs f)
computeHash f@Disj{}    = hash '|' `combine` hash (subfs f)
computeHash f@Diam{}    = hash 'D' `combine` hash (relSym f)
                                   `combine` hash (subf f)
computeHash f@Box{}     = hash 'B' `combine` hash (relSym f)
                                   `combine` hash (subf f)
computeHash f@At{}      = hash '@' `combine` hash (label f)
                                   `combine` hash (subf f)
computeHash f@Down{}    = hash 'd' `combine` hash (boundVar f)
                                   `combine` hash (subf f)
computeHash (Opaque f)  = hash  f

newtype HashOrd a = HashOrd{fromHashOrd :: a} deriving ( Read, Show )

instance (Eq a, Hashable a) => Eq (HashOrd a) where
    (HashOrd a) == (HashOrd b) = hash a == hash b && a == b

instance (Ord a, Hashable a) => Ord (HashOrd a) where
    compare (HashOrd a) (HashOrd b) = case compare (hash a) (hash b) of
                                        EQ  -> compare a b
                                        res -> res

data CachedHash a = CachedHash Hash a deriving ( Show )

cacheHash :: Hashable a => a -> CachedHash a
cacheHash a = CachedHash (hash a) a

fromCachedHash :: CachedHash a -> a
fromCachedHash (CachedHash _ a) = a

instance Hashable a => Hashable (CachedHash a) where
    hash (CachedHash h _) = h

instance Eq a => Eq (CachedHash a) where
    (CachedHash _ l) == (CachedHash _ r) = l == r

instance Ord a => Ord (CachedHash a) where
    compare (CachedHash _ l) (CachedHash _ r) = compare l r

nomHashes :: Formula f -> Set Hash
nomHashes = _nomHashes . attrib

computeNomHashes :: Formula f -> Set Hash
computeNomHashes form = comp form
    where comp :: Formula f -> Set Hash
          comp f@Nom{}    = insertIfNotVar (symbol f)    Set.empty
          comp f@NegNom{} = insertIfNotVar (negSymbol f) Set.empty
          comp f@At{}     = insertIfNotVar (label f)     (nomHashes $ subf f)
          comp f@Down{}   = nomHashes $ subf f
          comp f@Box{}    = nomHashes $ subf f
          comp f@Diam{}   = nomHashes $ subf f
          comp f@Disj{}   = foldl1' Set.union . map nomHashes $ subfs f
          comp f@Conj{}   = foldl1' Set.union . map nomHashes $ subfs f
          comp (Opaque f) = nomHashes f
          comp _          = Set.empty
          --
          insertIfNotVar n s | isVar n   = s
                             | otherwise = s `Set.union` (nomsIn n)
          nomsIn n  = maybe (singleton n) (insert n) (onInvToNom n nomHashes)
          singleton = Set.singleton . hash
          insert    = Set.insert    . hash

containsNom :: NomSym -> Formula f -> Bool
containsNom i g =  hash i `Set.member` nomHashes g && exactContainedIn g
  where exactContainedIn :: Formula f -> Bool
        exactContainedIn f@Nom{}    = isHere (symbol f)
        exactContainedIn f@NegNom{} = isHere (negSymbol f)
        exactContainedIn f@At{}     = isHere (label f) || containsNom i (subf f)
        exactContainedIn f@Down{}   = containsNom i (subf f)
        exactContainedIn f@Box{}    = containsNom i (subf f)
        exactContainedIn f@Diam{}   = containsNom i (subf f)
        exactContainedIn f@Disj{}   = any (containsNom i) (subfs f)
        exactContainedIn f@Conj{}   = any (containsNom i) (subfs f)
        exactContainedIn (Opaque f) = exactContainedIn f
        exactContainedIn _          = False
        --
        isHere n = i == n || fromMaybe False (onInvToNom n $ containsNom i)


---------------------------------------
-- QuickCheck stuff                  --
---------------------------------------

instance Arbitrary RelSym where
    arbitrary = oneof [liftM Rel    arbitrary,
                       liftM RelInv arbitrary,
                       return Univ]
    --
    coarbitrary (Rel    r) = variant 0 . coarbitrary r
    coarbitrary (RelInv r) = variant 1 . coarbitrary r
    coarbitrary  Univ      = variant 3

instance Arbitrary NomSym where
    arbitrary = sized arb
        where arb 0 = oneof [return NspyU, return Neval,
                             liftM Ni arbitrary, liftM X arbitrary]
              arb n = oneof [return NspyU,
                             return Neval,
                             liftM Ni arbitrary,
                             liftM X  arbitrary,
                             resize (n `div` 2) $ do
                                a <- arbitrary
                                let at_f = a :: AtFormula
                                case specialize at_f of
                                    AtNom f -> mkNomC $ onSubf neg f
                                    _       -> mkNomC at_f
                            ]
    --
    coarbitrary NspyU    = variant 0 . coarbitrary ()
    coarbitrary Neval    = variant 1 . coarbitrary ()
    coarbitrary (Ni i)   = variant 2 . coarbitrary i
    coarbitrary (Nc _ f) = variant 3 . coarbitrary (onSubf opaque f)
    coarbitrary (X  x)   = variant 4 . coarbitrary x


mkNomC :: Formula (At f) -> Gen NomSym
mkNomC f = do r <- arbitrary
              return (toNom $ onSubf (diam r) f)


prop_read_PropSym :: PropSym -> Bool
prop_read_PropSym p = p == (read . show $ p)

prop_read_RelSym :: RelSym -> Bool
prop_read_RelSym r = r == (read . show $ r)

prop_read_NomSym :: NomSym -> Bool
prop_read_NomSym i = i == (read . show $ i)

prop_read_Opaque :: Formula Opaque -> Bool
prop_read_Opaque f = f == (read . show $ f)

prop_read_AtNomOpaque :: Formula (At Opaque) -> Bool
prop_read_AtNomOpaque f = f == (read . show $ f)


prop_ord_trichotomy_NomSym :: NomSym -> NomSym -> Bool
prop_ord_trichotomy_NomSym = metap_trichotomy compare

prop_ord_irreflexive_NomSym :: NomSym ->  Bool
prop_ord_irreflexive_NomSym = metap_irreflexive compare

prop_ord_antisymmetric_NomSym :: NomSym -> NomSym -> Bool
prop_ord_antisymmetric_NomSym = metap_antisymmetric compare

prop_ord_transitive_NomSym :: NomSym -> NomSym -> NomSym -> Property
prop_ord_transitive_NomSym = metap_transitive compare

prop_ord_isTotalOrder_RelSym :: RelSym -> RelSym -> Property
prop_ord_isTotalOrder_RelSym = isTotalOrder

prop_ord_transitive_RelSym :: RelSym -> RelSym -> RelSym -> Property
prop_ord_transitive_RelSym = metap_transitive compare

prop_trichotomy_Opaque :: Formula Opaque -> Formula Opaque -> Bool
prop_trichotomy_Opaque = metap_trichotomy compare

prop_irreflexive_Opaque :: Formula Opaque -> Bool
prop_irreflexive_Opaque = metap_irreflexive compare

prop_antisymmetric_Opaque :: Formula Opaque -> Formula Opaque -> Bool
prop_antisymmetric_Opaque = metap_antisymmetric compare

prop_transitive_Opaque :: Formula Opaque
                       -> Formula Opaque
                       -> Formula Opaque
                       -> Property
prop_transitive_Opaque = metap_transitive compare

prop_subformulaProperty :: Formula Opaque -> Bool
prop_subformulaProperty f = all (f >) $ args f

prop_rewriteOrd :: Int
                -> Formula Opaque
                -> Formula Opaque
                -> Formula Opaque
                -> Bool
prop_rewriteOrd pos t s1 s2 = (s1 > s2) == (replace pos t s1 > replace pos t s2)

replace :: Int -> Formula a -> Formula Opaque -> Formula Opaque
replace 0  _         t = t
replace _  Top{}     t = t
replace _  Nom{}     t = t
replace _  Prop{}    t = t
replace _  NegTop{}  t = t
replace _  NegNom{}  t = t
replace _  NegProp{} t = t
--
replace n f@At{}   t = Opaque $ at   (label f)    $ replace (n`div`2) (subf f) t
replace n f@Diam{} t = Opaque $ diam (relSym f)   $ replace (n`div`2) (subf f) t
replace n f@Box{}  t = Opaque $ box  (relSym f)   $ replace (n`div`2) (subf f) t
replace n f@Down{} t = Opaque $ down (boundVar f) $ replace (n`div`2) (subf f) t
--
replace n f@Disj{} t = Opaque $ disj $ rep_list n (subfs f) t
replace n f@Conj{} t = Opaque $ conj $ rep_list n (subfs f) t
--
replace n (Opaque s) t = replace n s t

rep_list :: Int -> [Formula a] -> Formula Opaque -> [Formula Opaque]
rep_list n fs t = concat [first, [replace n' t_p t], rest]
    where (n', p)          = n `divMod` length fs
          (first,t_p:rest) = splitAt p $ map opaque fs


prop_admOrd_A2 :: AtFormula -> Bool
prop_admOrd_A2 f = case specialize f of
                       AtNom{} -> True
                       _       -> compareF (subf f) (nom $ label f) == GT

prop_admOrd_A3 :: AtFormula -> AtFormula -> Bool
prop_admOrd_A3 f1 f2 = case compareF (subf f1) (subf f2) of
                        EQ  -> True
                        neq -> neq == compareF f1 f2

prop_admOrd_A4 :: Formula (Diam Nom) -> Property
prop_admOrd_A4 dn = forAll containing_box_nom $ \f -> compareF f dn == GT
    where containing_box_nom :: Gen (Formula  Opaque)
          containing_box_nom = try_size (100 :: Int)
          --
          try_size t = do f <- arbitrary
                          if contains_box_nom (unNNF f)
                            then return f
                            else if (t == 0)
                                  then sized $ \s -> resize (s+1) (try_size 100)
                                  else try_size (t-1)
          --
          contains_box_nom (F.Box _ (F.Nom _)) = True
          contains_box_nom other               = F.composeFold False
                                                               (||)
                                                               contains_box_nom
                                                               other

prop_admOrd_A5 :: Formula (Box Nom) -> Formula (Diam Nom) -> Bool
prop_admOrd_A5 f1 f2 = compareF f1 f2 == GT


prop_killNom_kills :: NomSym -> NomSym -> Formula Opaque -> Bool
prop_killNom_kills i j f =  (not $ i `Set.member` noms_f)
                             || (j `Set.member` noms_f'
                                 && (i `Set.member` noms_j
                                     || (not $ i `Set.member` noms_f')))
    where noms_f  = nomSymbols . getSignature $ f
          noms_f' = nomSymbols . getSignature $ killNom i j f
          noms_j  = nomSymbols . getSignature $ (nom j :: Formula Nom)

unit_tests :: UnitTest
unit_tests = [
    ("read/show - PropSymbol",        runTest prop_read_PropSym),
    ("read/show - NomSymbol",         runTest prop_read_NomSym),
    ("read/show - RelSymbol",         runTest prop_read_RelSym),
    ("read/show - F Opaque",          runTest prop_read_Opaque),
    ("read/show - F (At Opaque)", runTest prop_read_AtNomOpaque),
    --
    ("ord trichotomy    - NomSymbol", runTest prop_ord_trichotomy_NomSym),
    ("ord irreflexive   - NomSymbol", runTest prop_ord_irreflexive_NomSym),
    ("ord antisymmetric - NomSymbol", runTest prop_ord_antisymmetric_NomSym),
    ("ord transitive    - NomSymbol", runTest prop_ord_transitive_NomSym),
    ("total order - RelSymbol",       runTest prop_ord_isTotalOrder_RelSym),
    ("transitive  - RelSymbol",       runTest prop_ord_transitive_RelSym),
    --
    ("trichotomy - Formula",          runTest prop_trichotomy_Opaque),
    ("irreflexive - Formula",         runTest prop_irreflexive_Opaque),
    ("antisymmetric - Formula",       runTest prop_antisymmetric_Opaque),
    ("transitive - Formula",          runTest prop_transitive_Opaque),
    ("subformula property",           runTest prop_subformulaProperty),
    ("rewrite ordering",              runTest prop_rewriteOrd),
    ("adm ord A2",                    runTest prop_admOrd_A2),
    ("adm ord A3",                    runTest prop_admOrd_A3),
    ("adm ord A4",                    runTest prop_admOrd_A4),
    ("adm ord A5",                    runTest prop_admOrd_A5),
    --
    ("killNom removes in to_nom",     runTest prop_killNom_kills)
  ]
