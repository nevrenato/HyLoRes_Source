{-# OPTIONS_GHC -fno-warn-incomplete-patterns #-}
module HyLoRes.Formula.Internal(
    module HyLoRes.Formula.TypeLevel,
    --
    Form(..),
    top, bot, nom, negNom, prop, negProp,
    conj, disj,
    diam, box, at, down,
    opaque,
    nnfAtFormula, unNNF, eqUnNNF, showDebug,
    --
    Attrib(..), attrib,
    --
    Atom(..), Negation(..), negSymbol,
    --
    HasSubformula(..), HasSubformulas(..), OnSubf(..), Flatten(..),
    --
    ModalOp(..), label, boundVar,
    --
    mapSig, replaceNom, instanceFreeVar,
    --
    nonOpaque, nonOpaque2,
    --
    metap_read_Opaque, metap_read_AtNomOpaque,
    unit_tests )

where

import Test.QuickCheck hiding ( label )
import HyLo.Test       ( UnitTest, runTest )
import Control.Monad   ( liftM, liftM2 )

import Text.Show.Functions ()

import Text.Read ( Read(..) )

import HyLo.Signature.Simple ( PropSymbol, NomSymbol, RelSymbol )

import qualified HyLo.Formula as F

import HyLo.Model ( ModelsRel(..), Model, valN )

import HyLoRes.Formula.TypeLevel

data Form n p r a f where
    Top     :: a -> Form n p r a Top
    NegTop  :: a -> Form n p r a (Neg Top)
    --
    Nom     :: a -> n -> Form n p r a Nom
    Prop    :: a -> p -> Form n p r a Prop
    --
    NegNom  :: a -> n -> Form n p r a (Neg Nom)
    NegProp :: a -> p -> Form n p r a (Neg Prop)
    --
    Disj    :: a -> [Form n p r a f] -> Form n p r a Disj
    Conj    :: a -> [Form n p r a f] -> Form n p r a Conj
    --
    Diam    :: a -> r -> Form n p r a f -> Form n p r a (Diam f)
    Box     :: a -> r -> Form n p r a f -> Form n p r a (Box f)
    --
    At      :: a -> n -> Form n p r a f -> Form n p r a (At f)
    --
    Down    :: a -> n -> Form n p r a f -> Form n p r a (Down f)
    --
    Opaque  :: Form n p r a f -> Form n p r a Opaque
    -- --------------
    -- IMPORTANT: As an invariant, Opaque (Opaque _) is an invalid term
    -- --------------

eqUnNNF :: (Eq n, Eq p, Eq r) => Form n p r a f -> Form n p r a g -> Bool
eqUnNNF f g = unNNF f == unNNF g


instance (Show n, Show p, Show r) => Show (Form n p r a f) where
    show = show . unNNF

instance Specializable (Form n p r a) where
  specialize f@(At _ _ Top{})               = AtTop     f
  specialize f@(At _ _ Prop{})              = AtProp    f
  specialize f@(At _ _ Nom{})               = AtNom     f
  --
  specialize f@(At _ _ NegTop{})            = AtNegTop  f
  specialize f@(At _ _ NegProp{})           = AtNegProp f
  specialize f@(At _ _ NegNom{})            = AtNegNom  f
  --
  specialize f@(At _ _ Disj{})              = AtDisj    f
  specialize f@(At _ _ Conj{})              = AtConj    f
  --
  specialize f@(At _ _ (Diam _ _ Nom{}))    = AtDiamNom f
  specialize (At a i (Diam b r (Opaque f))) = specialize (At a i (Diam b r f))
  specialize (At a i (Diam b r f))          = AtDiamF (At a i$Diam b r$Opaque f)
  specialize (At a i (Box  b r f))          = AtBoxF  (At a i$Box  b r$opaque f)
  --
  specialize (At a i (Down b x f))          = AtDownF (At a i$Down b x$opaque f)
  --
  specialize (At a i (Opaque f))            = specialize (At a i f)
  specialize (At _ _ f@At{})                = specialize f
  specialize f                              = error $ "NNF.specialize: " ++
                                                       showDebug f


data P = P deriving (Show, Read)
data N = N deriving (Show, Read)
data R = R deriving (Show, Read)

showDebug :: Form n p r a f -> String
showDebug = showDebugF . unNNF

showDebugF :: F.Formula n p r -> String
showDebugF = show . F.mapSig (const N) (const P) (const R)

instance (Read n, Read p, Read r, Attrib a n p r)
      => Read (Form n p r a Opaque) where
    readPrec = unsafeFromF =<< readPrec

instance (Read n, Read p, Read r, Attrib a n p r)
      => Read (Form n p r a (At Opaque)) where
    readPrec = asAtOpaque =<< readPrec
        where asAtOpaque :: (Monad m, Attrib a n p r)
                         => Form n p r a Opaque
                         -> m (Form n p r a (At Opaque))
              asAtOpaque (Opaque f@At{}) = return $ onSubf opaque f
              asAtOpaque  _              = fail "Not an at-formula"


instance (Read n,Read p,Read r,Attrib a n p r) => Read (Form n p r a (At Nom))
  where
    readPrec = asAtNom =<< readPrec
        where asAtNom :: (Monad m, Attrib a n p r)
                      => Form n p r a Opaque
                      -> m (Form n p r a (At Nom))
              asAtNom (Opaque f@(At _ _ Nom{})) = return f
              asAtNom _                         = fail "Not an equality"

instance (Read n,Read p,Read r,Attrib a n p r) => Read (Form n p r a (At Prop))
  where
    readPrec = asAtNom =<< readPrec
        where asAtNom :: (Monad m, Attrib a n p r)
                      => Form n p r a Opaque
                      -> m (Form n p r a (At Prop))
              asAtNom (Opaque f@(At _ _ Prop{})) = return f
              asAtNom _                          = fail "Not an at-prop"

instance (Read n, Read p, Read r, Attrib a n p r)
      => Read (Form n p r a (At (Diam Nom)))
  where
    readPrec = asAtNom =<< readPrec
      where asAtNom :: (Monad m, Attrib a n p r)
                    => Form n p r a Opaque
                    -> m (Form n p r a (At (Diam Nom)))
            asAtNom (Opaque f@(At _ _ (Diam _ _ Nom{}))) = return f
            asAtNom _                                    = fail "Not a relation"

class Attrib a n p r where
    -- | @computeAttrib f@ must not read @attrib f@.
    computeAttrib :: Form n p r a f -> a

instance Attrib () n p r where
    computeAttrib = const ()

top :: Attrib a n p r => Form n p r a Top
top = let f = Top a; a = computeAttrib f in f

bot :: Attrib a n p r => Form n p r a (Neg Top)
bot = let f = NegTop a; a = computeAttrib f in f

nom :: Attrib a n p r => n -> Form n p r a Nom
nom i = let f = Nom a i; a = computeAttrib f in f

negNom :: Attrib a n p r => n -> Form n p r a (Neg Nom)
negNom i = let f = NegNom a i; a = computeAttrib f in f

prop :: Attrib a n p r => p -> Form n p r a Prop
prop p = let f = Prop a p; a = computeAttrib f in f

negProp :: Attrib a n p r => p -> Form n p r a (Neg Prop)
negProp p = let f = NegProp a p; a = computeAttrib f in f

disj :: Attrib a n p r => [Form n p r a f] -> Form n p r a Disj
disj fs = let f = Disj a fs; a = computeAttrib f in f

conj :: Attrib a n p r => [Form n p r a f] -> Form n p r a Conj
conj fs = let f = Conj a fs; a = computeAttrib f in f

diam :: Attrib a n p r => r -> Form n p r a f -> Form n p r a (Diam f)
diam r g = let f = Diam a r g; a = computeAttrib f in f

box :: Attrib a n p r => r -> Form n p r a f -> Form n p r a (Box f)
box r g = let f = Box a r g; a = computeAttrib f in f

at :: Attrib a n p r => n -> Form n p r a f -> Form n p r a (At f)
at i g = let f = At a i g; a = computeAttrib f in f

down :: Attrib a n p r => n -> Form n p r a f -> Form n p r a (Down f)
down x g = let f = Down a x g; a = computeAttrib f in f

opaque :: Form n p r a f -> Form n p r a Opaque
opaque o_f@(Opaque _) = o_f
opaque f              = Opaque f

{-# INLINE nonOpaque #-}
nonOpaque :: (forall t . Form n p r a t -> b) -> Form n p r a t' -> b
nonOpaque fun (Opaque f') = fun f'
nonOpaque fun  f          = fun f

{-# INLINE nonOpaque2 #-}
nonOpaque2 :: (forall t s . Form n p r a t -> Form n p r a s -> c)
           -> (Form n p r a t' -> Form n p r a s' -> c)
nonOpaque2 fun f = nonOpaque (nonOpaque fun f)


maybeAddPrefix :: Attrib a n p r
               => n
               -> Form n p r a Opaque
               -> Form n p r a (At Opaque)
maybeAddPrefix _ (Opaque (At _ n f)) = at n (opaque f)
maybeAddPrefix i  opaque_f           = at i  opaque_f

unNNF :: Form n p r a f -> F.Formula n p r
unNNF (Top     _)     = F.Top
unNNF (NegTop  _)     = F.Neg F.Top
unNNF (Prop    _ p)   = F.Prop p
unNNF (NegProp _ p)   = F.Neg $ F.Prop p
unNNF (Nom     _ n)   = F.Nom n
unNNF (NegNom  _ n)   = F.Neg $ F.Nom n
unNNF (Disj    _ [f]) = unNNF f
unNNF (Disj    _ fs)  = foldr1 (F.:|:) $ map unNNF fs
unNNF (Conj    _ [f]) = unNNF f
unNNF (Conj    _ fs)  = foldr1 (F.:&:) $ map unNNF fs
unNNF (Diam    _ r f) = F.Diam r (unNNF f)
unNNF (Box     _ r f) = F.Box  r (unNNF f)
unNNF (At      _ n f) = F.At n (unNNF f)
unNNF (Down    _ x f) = F.Down x (unNNF f)
unNNF (Opaque  f)     = unNNF f

nnfAtFormula :: Attrib a n p r=>n -> F.Formula n p r -> Form n p r a (At Opaque)
nnfAtFormula n = maybeAddPrefix n . get . unsafeFromF . F.nnf
    where get = maybe (error $ "nnfAtFormula: Unexpected formula") id


unsafeFromF :: forall n p r a m . (Monad m, Attrib a n p r)
            => F.Formula n p r
            -> m (Form n p r a Opaque)
unsafeFromF        F.Top       = return $ Opaque top
unsafeFromF (F.Neg F.Top)      = return $ Opaque bot
unsafeFromF        F.Bot       = return $ Opaque bot
unsafeFromF (F.Neg F.Bot)      = return $ Opaque top
unsafeFromF        (F.Prop p)  = return $ Opaque (prop p)
unsafeFromF (F.Neg (F.Prop p)) = return $ Opaque (negProp p)
unsafeFromF        (F.Nom n)   = return $ Opaque (nom n)
unsafeFromF (F.Neg (F.Nom n))  = return $ Opaque (negNom n)
unsafeFromF f@(_ F.:&: _)      = (Opaque . conj) `liftM`
                                 (mapM unsafeFromF $ listifyC f)
unsafeFromF f@(_ F.:|: _)      = (Opaque . disj) `liftM`
                                 (mapM unsafeFromF $ listifyD f)
unsafeFromF (F.Diam r f)       = do op <- unsafeFromF f
                                    case op :: Form n p r a Opaque of
                                      Opaque g -> return $ Opaque (diam r g)
unsafeFromF (F.Box  r f)       = do op <- unsafeFromF f
                                    case op :: Form n p r a Opaque of
                                      Opaque g -> return $ Opaque (box  r g)
unsafeFromF (F.At n f)         = do op <- unsafeFromF f
                                    case op :: Form n p r a Opaque of
                                      Opaque g -> return $ Opaque (at n g)
unsafeFromF (F.Down x f)       = do op <- unsafeFromF f
                                    case op :: Form n p r a Opaque of
                                      Opaque g -> return $ Opaque (down x g)
unsafeFromF f                  = fail $ "unsafeFromF: Unexpected formula: " ++
                                        showDebugF f

listifyD :: F.Formula n p r -> [F.Formula n p r]
listifyD (f1 F.:|: f2) = listifyD f1 ++ listifyD f2
listifyD f             = [f]

listifyC :: F.Formula n p r -> [F.Formula n p r]
listifyC (f1 F.:&: f2) = listifyC f1 ++ listifyC f2
listifyC f             = [f]


instance (Ord w, Ord n, Ord p, Ord r)
      => ModelsRel (Model w n p r, w) (Form n p r a f) n p r where
    (m,w) |= f = (m,w) |= unNNF f

instance (Ord w, Ord n, Ord p, Ord r)
      => ModelsRel (Model w n p r) (Form n p r a (At f)) n p r where
    m |= f = (m, valN m $ label f) |= f

label :: Form n p r a (At f) -> n
label (At _ n _) = n

boundVar :: Form n p r a (Down f) -> n
boundVar (Down _ x _) = x

attrib :: Form n p r a f -> a
attrib (Top  a)      = a
attrib (Nom  a _)    = a
attrib (Prop a _)    = a
--
attrib (NegTop  a)   = a
attrib (NegNom  a _) = a
attrib (NegProp a _) = a
--
attrib (Disj a _)    = a
attrib (Conj a _)    = a
--
attrib (Diam a _ _)  = a
attrib (Box  a _ _)  = a
attrib (At   a _ _)  = a
attrib (Down a _ _)  = a
--
attrib (Opaque f)    = attrib f

class (Replace t s f_t f_s) => OnSubf t s f_t f_s where
    onSubf :: Attrib a n p r
           => (Form n p r a t -> Form n p r a s)
           -> Form n p r a f_t
           -> Form n p r a f_s

instance Negation g (Neg g) => OnSubf f g (Neg f) (Neg g) where
    onSubf fun NegTop{}    = neg (fun top)
    onSubf fun f@NegNom{}  = neg (fun $ subf f)
    onSubf fun f@NegProp{} = neg (fun $ subf f)

instance OnSubf f g (Diam f) (Diam g) where
    onSubf fun f@Diam{} = diam (relSym f) (fun $ subf f)

instance OnSubf f g (Box f) (Box g) where
    onSubf fun f@Box{} = box (relSym f) (fun $ subf f)

instance OnSubf f g (At f) (At g) where
    onSubf fun f@At{} = at (label f) (fun $ subf f)

instance OnSubf f g (Down f) (Down g) where
    onSubf fun f@Down{} = down (boundVar f) (fun $ subf f)


class HasSubformula t s | t -> s where
    subf :: Attrib a n p r => Form n p r a t -> Form n p r a s


instance HasSubformula (Neg f) f where
    subf NegTop{}      = top
    subf (NegProp _ p) = prop p
    subf (NegNom  _ i) = nom i

instance HasSubformula (Diam f) f where
    subf (Diam _ _ f) = f

instance HasSubformula (Box f) f where
    subf (Box  _ _ f) = f

instance HasSubformula (At f) f where
    subf (At   _ _ f) = f

instance HasSubformula (Down f) f where
    subf (Down _ _ f) = f

class HasSubformulas t where
    subfs :: Form n p r a t -> [Form n p r a Opaque]

instance HasSubformulas Conj where
    subfs (Conj _ fs) = map opaque fs

instance HasSubformulas Disj where
    subfs (Disj _ fs) = map opaque fs


class Flatten f flattened | f -> flattened where
    flatten   :: f -> flattened


instance Flatten (Form n p r a (At Nom)) (n, n) where
    flatten (At _ i (Nom _ j)) = (i,j)

instance Flatten (Form n p r a (At (Neg Nom))) (n, n) where
    flatten (At _ i (NegNom _ j)) = (i,j)

instance Flatten (Form n p r a (At Prop)) (n, p) where
    flatten (At _ i (Prop _ p)) = (i, p)

instance Flatten (Form n p r a (At (Neg Prop))) (n, p) where
    flatten (At _ i (NegProp _ p)) = (i, p)

instance Flatten (Form n p r a (At (Diam Nom))) (n, r, n) where
    flatten (At _ i (Diam _ r (Nom _ j))) = (i, r, j)


class ModalOp t where
    relSym :: Form n p r a t -> r

instance ModalOp (Diam f) where
    relSym (Diam _ r _) = r

instance ModalOp (Box f) where
    relSym (Box _ r _) = r


class Atom f b | f -> b where
    symbol     :: f -> b
    fromSymbol :: b -> f

instance Attrib a n p r => Atom (Form n p r a Top) () where
    symbol (Top _) = ()
    fromSymbol _   = top

instance Attrib a n p r => Atom (Form n p r a Prop) p where
    symbol (Prop _ p) = p
    fromSymbol p      = prop p

instance Attrib a n p r => Atom (Form n p r a Nom) n where
    symbol (Nom _ n) = n
    fromSymbol i     = nom i


negSymbol :: (Atom (Form n p r a t) s,Attrib a n p r)=>Form n p r a (Neg t) -> s
negSymbol = symbol . subf

class Negation t n_t | t -> n_t, n_t -> t where
    neg :: Attrib a n p r => Form n p r a t -> Form n p r a n_t

instance Negation Top (Neg Top) where
    neg Top{} = let f = NegTop a; a = computeAttrib f in f

instance Negation (Neg Top) Top where
    neg g@NegTop{} = subf g

instance Negation Nom (Neg Nom) where
    neg g@Nom{} = let f = NegNom a (symbol g); a = computeAttrib f in f

instance Negation (Neg Nom) Nom where
    neg g@NegNom{} = subf g

instance Negation Prop (Neg Prop) where
    neg g@Prop{} = let f = NegProp a (symbol g); a = computeAttrib f in f

instance Negation (Neg Prop) Prop where
   neg g@NegProp{} = subf g


instance Negation t n_t => Negation (Diam t) (Box n_t) where
    neg f@Diam{} = box (relSym f) (neg $ subf f)

instance Negation  t n_t => Negation (Box t) (Diam n_t) where
    neg f@Box{} = diam (relSym f) (neg $ subf f)

instance Negation t n_t => Negation (At t) (At n_t) where
    neg f@At{} = at (label f) (neg $ subf f)

instance Negation t n_t => Negation  (Down t) (Down n_t) where
    neg f@Down{} = down (boundVar f) (neg $ subf f)

instance Negation  Opaque Opaque where
   neg (Opaque f@Top{})     = Opaque $ neg f
   neg (Opaque f@Nom{})     = Opaque $ neg f
   neg (Opaque f@Prop{})    = Opaque $ neg f
   neg (Opaque f@NegTop{})  = Opaque $ neg f
   neg (Opaque f@NegNom{})  = Opaque $ neg f
   neg (Opaque f@NegProp{}) = Opaque $ neg f
   neg (Opaque f@Disj{})    = Opaque $ conj (map (neg . opaque) $ subfs f)
   neg (Opaque f@Conj{})    = Opaque $ disj (map (neg . opaque) $ subfs f)
   neg (Opaque f@Diam{})    = Opaque $ box  (relSym f) (neg . opaque $ subf f)
   neg (Opaque f@Box{})     = Opaque $ diam (relSym f) (neg . opaque $ subf f)
   neg (Opaque f@At{})      = Opaque $ at (label f) (neg . opaque $ subf f)
   neg (Opaque f@Down{})    = Opaque $ down (boundVar f) (neg . opaque $ subf f)
   neg (Opaque Opaque{})    = error "neg: opaque-opaque!"


mapSig :: (Attrib a n p r, Attrib b m q s)
       => (n -> m)
       -> (p -> q)
       -> (r -> s)
       -> Form n p r a f
       -> Form m q s b f
mapSig _  _  _  Top{}       = top
mapSig _  _  _  NegTop{}    = bot
--
mapSig fn _  _  f@Nom{}     = nom  (fn $ symbol f)
mapSig _  fp _  f@Prop{}    = prop (fp $ symbol f)
--
mapSig fn _  _  f@NegNom{}  = negNom  (fn $ negSymbol f)
mapSig _  fp _  f@NegProp{} = negProp (fp $ negSymbol f)
--
mapSig fn fp fr f@Disj{}    = disj (map (mapSig fn fp fr) $ subfs f)
mapSig fn fp fr f@Conj{}    = conj (map (mapSig fn fp fr) $ subfs f)
--
mapSig fn fp fr f@Diam{}    = diam (fr $ relSym f) (mapSig fn fp fr $ subf f)
mapSig fn fp fr f@Box{}     = box  (fr $ relSym f) (mapSig fn fp fr $ subf f)
--
mapSig fn fp fr f@At{}      = at  (fn $ label f) (mapSig fn fp fr $ subf f)
--
mapSig fn fp fr f@Down{}    = down (fn $ boundVar f) (mapSig fn fp fr $ subf f)
--
mapSig fn fp fr (Opaque f)  = Opaque (mapSig fn fp fr f)


replaceNom :: (Eq n,Attrib a n p r)=>n -> n -> Form n p r a f -> Form n p r a f
replaceNom i i' f@Nom{}    = if i == symbol f then nom i' else f
replaceNom i i' f@NegNom{} = if i == (symbol $ subf f) then negNom i' else f
replaceNom i i' f@At{}     = if i == label f
                                 then at i' (replaceNom i i' $ subf f)
                                 else onSubf (replaceNom i i') f
replaceNom i i' f@Disj{}   = disj [replaceNom i i' f' | f' <- subfs f]
replaceNom i i' f@Conj{}   = conj [replaceNom i i' f' | f' <- subfs f]
replaceNom i i' f@Diam{}   = onSubf (replaceNom i i') f
replaceNom i i' f@Box{}    = onSubf (replaceNom i i') f
replaceNom i i' f@Down{}   = if i == boundVar f
                                 then down i' (replaceNom i i' $ subf f)
                                 else onSubf (replaceNom i i') f
replaceNom i i' (Opaque f) = Opaque (replaceNom i i' f)
replaceNom _ _   f         = f

instanceFreeVar :: (Eq n, Attrib a n p r)
                => n
                -> n
                -> Form n p r a f
                -> Form n p r a f
instanceFreeVar i i' f@Nom{}    = if i == symbol f then nom i' else f
instanceFreeVar i i' f@NegNom{} = if i == negSymbol f
                                      then negNom i'
                                      else f
instanceFreeVar i i' f@At{}     = if i == label f
                                      then at i' (instanceFreeVar i i' $ subf f)
                                      else onSubf (instanceFreeVar i i') f
instanceFreeVar i i' f@Disj{}   = disj [instanceFreeVar i i' f' | f' <- subfs f]
instanceFreeVar i i' f@Conj{}   = conj [instanceFreeVar i i' f' | f' <- subfs f]
instanceFreeVar i i' f@Diam{}   = onSubf (instanceFreeVar i i') f
instanceFreeVar i i' f@Box{}    = onSubf (instanceFreeVar i i') f
instanceFreeVar i i' f@Down{}   = if i == boundVar f
                                      then f
                                      else onSubf (instanceFreeVar i i') f
instanceFreeVar i i' (Opaque f)  = Opaque (instanceFreeVar i i' f)
instanceFreeVar _ _   f          = f


---------------------------------------
-- QuickCheck stuff                  --
---------------------------------------

instance (Arbitrary n, Arbitrary p, Arbitrary r, Eq n, Attrib a n p r)
      => Arbitrary (Form n p r a Opaque) where
    arbitrary   = do f <- arbitrary
                     return (subf $ nnfAtFormula undefined (removeUniversals f))
    --
    coarbitrary = coarbitrary . unNNF

removeUniversals :: F.Formula n p r -> F.Formula n p r
removeUniversals (F.A f) = removeUniversals f
removeUniversals (F.E f) = removeUniversals f
removeUniversals (F.D f) = removeUniversals f
removeUniversals (F.B f) = removeUniversals f
removeUniversals f       = F.composeMap id removeUniversals f

instance (Arbitrary n, Arbitrary p, Arbitrary r, Attrib a n p r)
      => Arbitrary (Form n p r a Top)
  where
    arbitrary   = return top
    coarbitrary = const $ coarbitrary ()

instance (Arbitrary n, Arbitrary p, Arbitrary r, Attrib a n p r)
      => Arbitrary (Form n p r a Prop)
  where
    arbitrary = liftM fromSymbol arbitrary
    --
    coarbitrary = coarbitrary . unNNF

instance (Arbitrary n, Arbitrary p, Arbitrary r, Attrib a n p r)
      => Arbitrary (Form n p r a Nom)
  where
    arbitrary = liftM fromSymbol arbitrary
    --
    coarbitrary = coarbitrary . unNNF

instance (Arbitrary n, Arbitrary p, Arbitrary r, Attrib a n p r)
      => Arbitrary (Form n p r a (Neg Prop)) where
    arbitrary = liftM negProp arbitrary
    --
    coarbitrary = coarbitrary . unNNF

instance (Arbitrary n, Arbitrary p, Arbitrary r, Attrib a n p r)
      => Arbitrary (Form n p r a (Neg Nom)) where
    arbitrary = liftM negNom arbitrary
    --
    coarbitrary = coarbitrary . unNNF

instance (Arbitrary n, Arbitrary p, Arbitrary r,
          Arbitrary (Form n p r a f), Attrib a n p r)
      => Arbitrary (Form n p r a (At f)) where
    arbitrary   = liftM2 at arbitrary arbitrary
    --
    coarbitrary = coarbitrary . unNNF

instance (Arbitrary n, Arbitrary p, Arbitrary r,
          Arbitrary (Form n p r a f), Attrib a n p r)
      => Arbitrary (Form n p r a (Down f)) where
    arbitrary   = liftM2 down arbitrary arbitrary
    --
    coarbitrary = coarbitrary . unNNF

instance (Arbitrary n, Arbitrary p, Arbitrary r,
          Arbitrary (Form n p r a f), Attrib a n p r)
      => Arbitrary (Form n p r a (Diam f)) where
    arbitrary   = liftM2 diam arbitrary arbitrary
    --
    coarbitrary = coarbitrary . unNNF

instance (Arbitrary n, Arbitrary p, Arbitrary r,
          Arbitrary (Form n p r a f), Attrib a n p r)
      => Arbitrary (Form n p r a (Box f)) where
    arbitrary   = liftM2 box arbitrary arbitrary
    --
    coarbitrary = coarbitrary . unNNF

instance (Arbitrary n, Arbitrary p, Arbitrary r, Eq n, Attrib a n p r)
      => Arbitrary (Form n p r a Disj) where
    arbitrary   = do (f,fs) <- arbitrary
                     return $ disj (f:fs :: [Form n p r a Opaque])
    --
    coarbitrary = coarbitrary . unNNF

instance (Arbitrary n, Arbitrary p, Arbitrary r, Eq n, Attrib a n p r)
      => Arbitrary (Form n p r a Conj) where
    arbitrary   = do (f,fs) <- arbitrary
                     return $ conj (f:fs :: [Form n p r a Opaque])
    --
    coarbitrary = coarbitrary . unNNF


metap_read_NNF :: (Show (Form n p r a f), Read (Form n p r a f),
                   Arbitrary (Form n p r a f), Attrib a n p r,
                   Eq n, Eq p, Eq r)
                => Form n p r a f -> Bool
metap_read_NNF f = eqUnNNF f f'
    where f' = (read $ show f) `asTypeOf` f

metap_read_Opaque :: (Show      (Form n p r a Opaque),
                      Read      (Form n p r a Opaque),
                      Arbitrary (Form n p r a Opaque),
                      Eq n, Eq p, Eq r,
                      Attrib a n p r)
                   => Form n p r a Opaque -> Bool
metap_read_Opaque = metap_read_NNF

metap_read_AtNomOpaque :: (Show      (Form n p r a (At Opaque)),
                           Read      (Form n p r a (At Opaque)),
                           Arbitrary (Form n p r a (At Opaque)),
                           Eq n, Eq p, Eq r,
                           Attrib a n p r)
                        => Form n p r a (At Opaque) -> Bool
metap_read_AtNomOpaque = metap_read_NNF

type TestFormula f = Form NomSymbol PropSymbol RelSymbol () f

prop_read_Opaque :: TestFormula Opaque -> Bool
prop_read_Opaque = metap_read_Opaque

prop_read_AtNomOpaque :: TestFormula (At Opaque) -> Bool
prop_read_AtNomOpaque = metap_read_AtNomOpaque

prop_mapSig :: (NomSymbol -> NomSymbol)
            -> (PropSymbol -> PropSymbol)
            -> (RelSymbol -> RelSymbol)
            -> TestFormula (At Opaque)
            -> Bool
prop_mapSig fn fp fr f = (unNNF mapSig_f) == (F.mapSig fn fp fr . unNNF $ f)
    where mapSig_f = (mapSig fn fp fr $ f) :: TestFormula (At Opaque)

prop_replaceNom :: NomSymbol -> NomSymbol -> TestFormula Opaque -> Bool
prop_replaceNom i j f = eqUnNNF (replaceNom i j f) (mapSig (repl i j) id id f)
    where repl a b c = if c == a then b else c

prop_instFreeVarSameBnds :: NomSymbol -> NomSymbol -> TestFormula Opaque -> Bool
prop_instFreeVarSameBnds  x i f = boundVars f == boundVars f'
    where f' = instanceFreeVar x i f
          boundVars = F.boundVars . unNNF

prop_instFreeVarRepl :: NomSymbol -> NomSymbol -> TestFormula Opaque -> Property
prop_instFreeVarRepl x i f = (null . F.boundVars $ unNNF f) ==>
                              eqUnNNF (instanceFreeVar x i f) (replaceNom x i f)

prop_spec_rel_opaque :: TestFormula (At (Diam Nom)) -> Bool
prop_spec_rel_opaque f = case specialize (onSubf (onSubf opaque) f) of
                             AtDiamNom f' -> eqUnNNF f f'
                             _            -> False

unit_tests :: UnitTest
unit_tests = [
    ("read/show - F Opaque",       runTest prop_read_Opaque),
    ("read/show - F (At Opaque)",  runTest prop_read_AtNomOpaque),
    ("mapSig works",               runTest prop_mapSig),
    ("replaceNom/mapSig",          runTest prop_replaceNom),
    ("instanceFreeVar/bound vars", runTest prop_instFreeVarSameBnds),
    ("instanceFreeVar/replaceNom", runTest prop_instFreeVarRepl),
    ("specialize - Rel Opaque",    runTest prop_spec_rel_opaque)
  ]


