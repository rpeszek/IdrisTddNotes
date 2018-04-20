{-# LANGUAGE 
     GADTs
   , KindSignatures
   , DataKinds
   , TypeOperators 
   , TypeFamilies
   , StandaloneDeriving
   , RankNTypes
   , UndecidableInstances -- needed to define ToTL and FromTL 
#-}
{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}

module Util.NonLitsNatAndVector where
import qualified GHC.TypeLits as TL
  
data Nat = Z | S Nat deriving Show

natToInteger :: Nat -> Integer
natToInteger Z = 0
natToInteger (S un) = 1 + (natToInteger un)

{- Called often Natty, allows to work with Nats as Types -}
data SNat (n :: Nat) where
  SZ :: SNat Z
  SS :: SNat n -> SNat (S n)

deriving instance Show (SNat n)

sNatToInteger :: SNat n -> Integer 
sNatToInteger = natToInteger . sNatToNat

sNatToNat :: SNat n -> Nat 
sNatToNat SZ = Z
sNatToNat (SS sn) = S (sNatToNat sn)


{-| Existential reification 
   I am following Haskell naming convention 
-}
data SomeNat where
    SomeNat :: SNat n -> SomeNat

sNatToSomeNat :: SNat n -> SomeNat 
sNatToSomeNat = SomeNat

natToSomeNat :: Nat -> SomeNat
natToSomeNat Z = SomeNat SZ
natToSomeNat (S k) = case natToSomeNat k of
               SomeNat n -> SomeNat $ SS n

someNatToInteger :: SomeNat -> Integer
someNatToInteger (SomeNat SZ) = 0
someNatToInteger (SomeNat (SS un)) = 1 + (someNatToInteger $ SomeNat un)

{-| CPS style reification 
-}
withNat :: Nat -> (forall n. SNat n -> r) -> r
withNat k = withSomeNat $ natToSomeNat k 

withSomeNat :: SomeNat -> (forall n. SNat n -> r) -> r
withSomeNat (SomeNat n) f = f n

{- Implicit SNat evidence, mimics singletons SingI -}
class SNatI (n :: Nat) where
  sNat :: SNat n

instance SNatI 'Z where sNat = SZ
instance SNatI k => SNatI ('S k) where sNat = SS sNat

data Vect (n::Nat) a where
  Nil :: Vect 'Z a
  (:::) :: a -> Vect n a -> Vect ('S n) a
infixr 5 :::

deriving instance Show a => Show (Vect n a)

vlength :: Vect n a -> SNat n  
vlength Nil = SZ
vlength (x ::: xs) = SS (vlength xs)

{- Mimics Idris -}
type family (m :: Nat) + (n :: Nat) :: Nat where
   Z + right = right 
   (S left) + right = S (left + right) 

type family ToTL (n :: Nat) :: TL.Nat where
    ToTL Z = 0
    ToTL (S n) = 1 TL.+ (ToTL n)

type family FromTL (n :: TL.Nat) :: Nat where
    FromTL 0 = Z
    FromTL n = S (FromTL (n TL.- 1))

{-| reification type -}
data SomeVect a where
   SomeVect :: SNat s -> Vect s a -> SomeVect a

{-| CPS style reification -}
withSomeVect :: SomeVect a -> (forall n. SNat n -> Vect n a -> r) -> r
withSomeVect (SomeVect sn vec) f = f sn vec
