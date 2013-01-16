module HyLoRes.Formula.TypeLevel

where

data Top

data Prop
data Nom

data Neg f

data Disj
data Conj

data Diam f
data Box f
data At f
data Down f

data Opaque

class IsSubformula  f_a a | f_a -> a

instance IsSubformula (Neg  f) f
instance IsSubformula (Diam f) f
instance IsSubformula (Box  f) f
instance IsSubformula (At   f) f
instance IsSubformula (Down f) f

class (IsSubformula f_a a, IsSubformula f_b b)
   => Replace a b f_a f_b | f_a a   b -> f_b,
                              a b f_b -> f_a,
                            f_a a f_b ->   b,
                            f_a b f_b ->   a

instance Replace a b (Neg  a) (Neg  b)
instance Replace a b (Diam a) (Diam b)
instance Replace a b (Box  a) (Box  b)
instance Replace a b (At   a) (At   b)
instance Replace a b (Down a) (Down b)


data Spec a = AtTop     (a (At Top))
            | AtProp    (a (At Prop))
            | AtNom     (a (At Nom))
            --
            | AtNegTop  (a (At (Neg Top)))
            | AtNegProp (a (At (Neg Prop)))
            | AtNegNom  (a (At (Neg Nom)))
            --
            | AtConj    (a (At Conj))
            | AtDisj    (a (At Disj))
            --
            | AtDiamNom (a (At (Diam Nom)))
            | AtDiamF   (a (At (Diam Opaque)))
            | AtBoxF    (a (At (Box Opaque)))
            --
            | AtDownF   (a (At (Down Opaque)))

class Specializable a where
  specialize:: a (At t) -> Spec a

instance Show (Spec a) where
    show AtTop{}     = "AtTop"
    show AtProp{}    = "AtProp"
    show AtNom{}     = "AtNom"
    --
    show AtNegTop{}  = "AtNegTop"
    show AtNegProp{} = "AtNegProp"
    show AtNegNom{}  = "AtNegNom"
    --
    show AtConj{}    = "AtConj"
    show AtDisj{}    = "AtDisj"
    --
    show AtDiamNom{} = "AtDiamNom"
    show AtDiamF{}   = "AtDiamF"
    show AtBoxF{}    = "AtBoxF"
    --
    show AtDownF{}   = "AtDownF"
