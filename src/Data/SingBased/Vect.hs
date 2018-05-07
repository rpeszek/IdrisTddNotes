
{-# LANGUAGE 
      KindSignatures
      , DataKinds
      , GADTs
      -- , PolyKinds
      , TypeInType -- needed for SVect
      , TypeOperators 
      , TypeFamilies
      , StandaloneDeriving
      , ScopedTypeVariables
      -- , TypeSynonymInstances
      , Rank2Types
#-}

module Data.SingBased.Vect where
import Numeric.Natural
import Data.Singletons
import Data.SingBased.Nat
import qualified GHC.TypeLits as TL

{- Vect stuff -}   

data Vect (n :: Nat) a where
     VNil :: Vect 'Z a
     (:::) :: a -> Vect n a -> Vect ('S n) a
infixr 5 :::

deriving instance Show a => Show (Vect n a)

vlength :: Vect n a -> SNat n  
vlength VNil = SZ
vlength (x ::: xs) = SS (vlength xs)

{-| simple reification type, I decided to include SNat for now, this is redundant as
vlenght recovers it but is isomorphic to dependent pair concept in Idris -}
data SomeVect a where
   SomeVect :: SNat s -> Vect s a -> SomeVect a

deriving instance Show a => Show (SomeVect a)

{-| CPS style reification -}
withSomeVect :: SomeVect a -> (forall n. SNat n -> Vect n a -> r) -> r
withSomeVect (SomeVect sn vec) f = f sn vec

listToSomeVect :: [a] -> SomeVect a
listToSomeVect [] = SomeVect SZ VNil
listToSomeVect (x : xs) 
      = case listToSomeVect xs of SomeVect n rr -> SomeVect (SS n) (x ::: rr) 


vectToList :: Vect n a -> [a]
vectToList VNil = []
vectToList (x ::: xs) = x : vectToList xs


{-| TODO This would be more general since Vect :: Nat -> Type -> Type, currently not used-}
{-
data VectK (n :: Nat) (a :: k) where
     VNilK :: VectK 'Z a
     ConsK :: Sing a -> VectK n a -> VectK ('S n) a

-}

data SVect (v :: Vect n a) where
  SVNil :: SVect  'VNil
  SVCons :: Sing a -> SVect xs -> SVect (a '::: xs)

sVectToVect :: forall a (n :: Nat) (xs :: Vect n a) . SingKind a => SVect xs -> Vect n (Demote a)
sVectToVect SVNil = VNil
sVectToVect (SVCons sa sxs) = (fromSing sa) ::: sVectToVect sxs

data SomeKnownSizeVect (n:: Nat) a where
   MkSomeKnownSizeVect :: SNat n -> SVect (v :: Vect n a) -> SomeKnownSizeVect n a

someKnownSizeVectToVect :: SingKind a => SomeKnownSizeVect n a -> Vect n (Demote a)
someKnownSizeVectToVect ksv = case ksv of MkSomeKnownSizeVect _ sv -> sVectToVect sv

type family VOneElem (x :: a) :: Vect (S Z) a where
  VOneElem x = x '::: 'VNil

type family VAppend (v1 :: Vect n a) (v2 :: Vect m a) :: Vect (Plus n m) a where
  VAppend 'VNil xs = xs
  VAppend (y '::: ys) xs = y '::: VAppend ys xs
