{-# LANGUAGE 
     GADTs
   , KindSignatures
   , DataKinds
   , TypeOperators 
   , TypeFamilies
   , StandaloneDeriving
   , UndecidableInstances -- needed to define ToTL and FromTL 
#-}

module Util.NonLitsNatAndVector where
import qualified GHC.TypeLits as TL
  
data Nat = Z | S Nat deriving Show

{- Called often Natty, allows to work with Nats as Types -}
data SNat (n :: Nat) where
  SZ :: SNat Z
  SS :: SNat n -> SNat (S n)

deriving instance Show (SNat n)

sNatToInteger :: SNat n -> Integer 
sNatToInteger SZ = 0
sNatToInteger (SS sn) = 1 + (sNatToInteger sn)

data UnknownNat where
  UZ :: UnknownNat
  US :: UnknownNat -> UnknownNat

sNatToUnknownNat :: SNat n -> UnknownNat 
sNatToUnknownNat SZ = UZ
sNatToUnknownNat (SS sn) = US (sNatToUnknownNat sn)

unknownNatToInteger :: UnknownNat -> Integer
unknownNatToInteger UZ = 0
unknownNatToInteger (US un) = 1 + (unknownNatToInteger un)

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
