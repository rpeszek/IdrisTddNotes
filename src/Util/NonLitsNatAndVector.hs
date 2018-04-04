{-# LANGUAGE 
     GADTs
   , KindSignatures
   , DataKinds
   -- , TypeOperators 
   -- , TypeFamilies
   -- , StandaloneDeriving
   -- , UndecidableInstances
#-}

module Util.NonLitsNatAndVector where
  
data Nat = Z | S Nat 

data SNat (n :: Nat) where
  SZ :: SNat Z
  SS :: SNat n -> SNat (S n)

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
