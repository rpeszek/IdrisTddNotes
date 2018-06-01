
{-# LANGUAGE 
      KindSignatures
      , DataKinds
      , GADTs
      -- , PolyKinds
      , TypeInType 
      , TypeOperators 
      , TypeFamilies
      , StandaloneDeriving
      , ScopedTypeVariables
      -- , TypeSynonymInstances
      , Rank2Types
#-}
{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}

module Data.SingBased.Vect where

import Data.Kind (Type)
import Numeric.Natural
import Data.Singletons
import Data.SingBased.Nat
import Data.SingBased.List
import qualified GHC.TypeLits as TL
import Data.Type.Equality ((:~:)(Refl), sym)
import Unsafe.Coerce

------------------------------------------------------
---- main part                ------------------------
------------------------------------------------------

data Vect (n :: Nat) a where
     VNil :: Vect 'Z a
     (:::) :: a -> Vect n a -> Vect ('S n) a
infixr 5 :::

deriving instance Show a => Show (Vect n a)

vlength :: Vect n a -> SNat n  
vlength VNil = SZ
vlength (x ::: xs) = SS (vlength xs)

------------------------------------------------------
---- singletons boilder plate ------------------------
------------------------------------------------------

data instance Sing ( v :: Vect n a) :: Type where
  SVNil :: Sing VNil
  SVCons :: Sing a -> Sing v -> Sing ((:::) a v)

type VNilSym0 = VNil

data VConsSym0 :: a ~> Vect n a ~> Vect (S n) a
type instance Apply VConsSym0 a = VConsSym1 a

data VConsSym1 :: a -> Vect n a ~> Vect (S n) a
type instance Apply (VConsSym1 a) b = VConsSym2 a b

type VConsSym2 a b = (:::) a b

instance SingI VNil where
  sing = SVNil
instance (SingI h, SingI t) =>
           SingI ((:::) (h :: k) (t :: Vect n k)) where
  sing = SVCons sing sing


sVectToVect :: forall a (n :: Nat) (xs :: Vect n a) . SingKind a => Sing xs -> Vect n (Demote a)
sVectToVect SVNil = VNil
sVectToVect (SVCons sa sxs) = (fromSing sa) ::: sVectToVect sxs

-- | this does not seem much more useful that using Vect n (Demote k)
-- should be equivalent to use of SomeKnownSizeVect 
-- could be useful for more polymorphic reasons
instance SingKind k => SingKind (Vect n k) where
  type Demote (Vect n k) = Vect n (Demote k)
  fromSing SVNil = VNil
  fromSing (SVCons h t) = (:::) (fromSing h) (fromSing t)
  toSing VNil = SomeSing SVNil
  toSing ((:::) h t) = let nv = vlength t in
    case ( toSing h :: SomeSing k
         , unsafeCoerce (toSing t) ) of
      (SomeSing h', SomeSing t') -> SomeSing $ SVCons h' t'

{-
ghci> :t toSing $ Z ::: (S Z) ::: VNil
toSing $ Z ::: (S Z) ::: VNil :: SomeSing (Vect ('S ('S 'Z)) Nat)
ghci> withSomeSing (Z ::: (S Z) ::: VNil) sVectToVect
Z ::: (S Z ::: VNil)
ghci> fromSing $ (SS SZ) `SVCons` SVNil
S Z ::: VNil
-}

---------------------------------------------------------------------------
---- by hand (some could be replaced with std singletons sugar)   ---------
---------------------------------------------------------------------------

{-| Also see SomeSVect and SomeKnownSizeVect below.
simple reification type, I decided to include SNat for now, this is redundant as
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


{-| TODO This would be more general -}
{-
data VectK (n :: Nat) (a :: k) where
     VNilK :: VectK 'Z a
     ConsK :: Sing a -> VectK n a -> VectK ('S n) a
-}


data SomeKnownSizeVect (n:: Nat) k where
   MkSomeKnownSizeVect :: SNat n -> Sing (v :: Vect n k) -> SomeKnownSizeVect n k

vectToSomeKnownSizeVect :: SingKind k => Vect n (Demote k) -> SomeKnownSizeVect n k
vectToSomeKnownSizeVect VNil = MkSomeKnownSizeVect SZ SVNil
vectToSomeKnownSizeVect (x ::: xs) = case toSing x of
                 SomeSing sx -> case vectToSomeKnownSizeVect xs of
                  MkSomeKnownSizeVect k sxs -> MkSomeKnownSizeVect (SS k) (SVCons sx sxs)

someKnownSizeVectToVect :: SingKind k => SomeKnownSizeVect n k -> Vect n (Demote k)
someKnownSizeVectToVect ksv = case ksv of MkSomeKnownSizeVect _ sv -> sVectToVect sv

{-
ghci> :t MkSomeKnownSizeVect (SS SZ) $ SVCons s1 SVNil
MkSomeKnownSizeVect (SS SZ) $ SVCons s1 SVNil
  :: SomeKnownSizeVect ('S 'Z) Nat

ghci> someKnownSizeVectToVect $ MkSomeKnownSizeVect (SS SZ) $ SVCons s1 SVNil
S Z ::: VNil
-}

data SomeSVect k where
  SomeSVect :: SNat n -> Sing (v :: Vect n k) -> SomeSVect k
 
vectToSomeSVect :: SingKind k => Vect n (Demote k) -> SomeSVect k
vectToSomeSVect v = case vectToSomeKnownSizeVect v of
      MkSomeKnownSizeVect k xs -> SomeSVect k xs


type family VOneElem (x :: a) :: Vect (S Z) a where
  VOneElem x = x '::: 'VNil

sVOneElem :: Sing x -> Sing (x '::: 'VNil)
sVOneElem x = SVCons x SVNil

type family VAppend (v1 :: Vect n a) (v2 :: Vect m a) :: Vect (Plus n m) a where
  VAppend 'VNil xs = xs
  VAppend (y '::: ys) xs = y '::: VAppend ys xs

sVAppend :: Sing v1 -> Sing v2 -> Sing (VAppend v1 v2)
sVAppend SVNil xs = xs
sVAppend (SVCons y ys) xs = SVCons y (sVAppend ys xs)
