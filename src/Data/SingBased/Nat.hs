{-
"Singling of literal patterns not yet supported"
TODO move Nat into a separate module
-}

{-# LANGUAGE TemplateHaskell
      , KindSignatures
      , DataKinds
      , GADTs
      , PolyKinds
      , TypeInType -- needed for SVect
      , TypeOperators 
      , TypeFamilies
      , StandaloneDeriving
      , UndecidableInstances 
      , ScopedTypeVariables
      , TypeSynonymInstances
      , Rank2Types
#-}
{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}

module Data.SingBased.Nat where
import Numeric.Natural
import Data.Singletons.TH
import qualified GHC.TypeLits as TL

$(singletons [d|
  data Nat = Z | S Nat
    deriving (Show, Eq)

  plus :: Nat -> Nat -> Nat
  plus Z m = m
  plus (S n) m = S (plus n m)
  infixl 6 `plus`

  multi :: Nat -> Nat -> Nat
  multi Z m = Z
  multi (S n) m = plus (multi n m) m
  infixl 7 `multi`

  half :: Nat -> Nat 
  half Z = Z
  half (S Z) = Z
  half (S (S k)) = S (half k)
  |])

instance Ord Nat where
  compare Z Z = EQ
  compare Z _    = LT
  compare _  Z = GT
  compare (S m) (S n) = compare m n

instance Show (SNat n) where
  show  = show . fromSing

natToInteger :: Nat -> Integer
natToInteger Z = 0
natToInteger (S un) = 1 + (natToInteger un)

withInteger :: Integer -> (Nat -> Nat) -> Integer
withInteger i f = natToInteger $ f (integerToNat i)

someNatToInteger :: SomeSing Nat -> Integer
someNatToInteger (SomeSing n) = natToInteger (fromSing n)

-- partial
integerToNat :: Integer -> Nat
integerToNat n 
        | n < 0 = error "negative integer"
        | n == 0 = Z
        | otherwise = S (integerToNat (n - 1))

-- Singling of literal patterns not yet supported
type family ToTL (n :: Nat) :: TL.Nat where
    ToTL Z = 0
    ToTL (S n) = 1 TL.+ (ToTL n)

type family FromTL (n :: TL.Nat) :: Nat where
    FromTL 0 = Z
    FromTL n = S (FromTL (n TL.- 1))

type family (m :: Nat) + (n :: Nat) :: Nat where
   left + right = Plus left right 


s0 :: SNat (FromTL 0) -- 'Z
s0 = SZ
s1 :: SNat (FromTL 1) -- ('S 'Z)
s1 = SS s0
s2 :: SNat (FromTL 2) -- ('S ('S 'Z))
s2 = SS s1
s3 :: SNat (FromTL 3) -- ('S ('S ('S 'Z)))
s3 = SS s2
s4 :: SNat (FromTL 4) -- ('S ('S ('S 'Z)))
s4 = SS s3
