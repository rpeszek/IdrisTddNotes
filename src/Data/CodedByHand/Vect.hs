{-# LANGUAGE 
     GADTs
   , KindSignatures
   , DataKinds
   , TypeOperators 
   , TypeFamilies
   , StandaloneDeriving
   , Rank2Types
#-}
{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}

module Data.CodedByHand.Vect where
import qualified GHC.TypeLits as TL
import Data.CodedByHand.Nat 


data Vect (n::Nat) a where
  VNil :: Vect 'Z a
  (:::) :: a -> Vect n a -> Vect ('S n) a
infixr 5 :::

deriving instance Show a => Show (Vect n a)

vlength :: Vect n a -> SNat n  
vlength VNil = SZ
vlength (x ::: xs) = SS (vlength xs)


{-| reification type, I decided to exclude SNat, since I can recover it using
vlenght, this makes is slightly different than the dependent pair concept in Idris -}
data SomeVect a where
   SomeVect :: {- SNat n -> -} Vect n a -> SomeVect a

deriving instance Show a => Show (SomeVect a)

{-| CPS style reification -}
withSomeVect :: SomeVect a -> (forall n.Vect n a -> r) -> r
withSomeVect (SomeVect vec) f = f vec

listToSomeVect :: [a] -> SomeVect a
listToSomeVect [] = SomeVect VNil
listToSomeVect (x : xs) 
      = case listToSomeVect xs of SomeVect rr -> SomeVect (x ::: rr) 

vectToList :: Vect n a -> [a]
vectToList VNil = []
vectToList (x ::: xs) = x : vectToList xs

listWithVect :: [a] -> (forall n. Vect n a -> r) -> r
listWithVect xs f = case listToSomeVect xs of
      SomeVect vxs -> f vxs 
