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
#-}

module Util.SingVector where
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
   

data Vect (n :: Nat) a where
     Nil :: Vect 'Z a
     (:::) :: a -> Vect n a -> Vect ('S n) a
infixr 5 :::

vlength :: Vect n a -> SNat n  
vlength Nil = SZ
vlength (x ::: xs) = SS (vlength xs)

{- TODO This would be more general since Vect :: Nat -> Type -> Type -}
data VectK (n :: Nat) (a :: k) where
     NilK :: VectK 'Z a
     ConsK :: Sing a -> VectK n a -> VectK ('S n) a

deriving instance Show a => Show (Vect n a)

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


-- Currently, I do not know how to do singletons for the Vect itself

data SVect (v :: Vect n a) where
  SNil :: SVect  'Nil
  SCons :: Sing a -> SVect xs -> SVect (a '::: xs)

sVectToVect :: forall a (n :: Nat) (xs :: Vect n a) . SingKind a => SVect xs -> Vect n (Demote a)
sVectToVect SNil = Nil
sVectToVect (SCons sa sxs) = (fromSing sa) ::: sVectToVect sxs

data SomeKnownSizeVect (n:: Nat) a where
   MkSomeKnownSizeVect :: SNat n -> SVect (v :: Vect n a) -> SomeKnownSizeVect n a

someKnownSizeVectToVect :: SingKind a => SomeKnownSizeVect n a -> Vect n (Demote a)
someKnownSizeVectToVect ksv = case ksv of MkSomeKnownSizeVect _ sv -> sVectToVect sv
