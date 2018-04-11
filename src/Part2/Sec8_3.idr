module Part2.Sec8_3
import Data.Vect

{-
data Dec : (prop : Type) -> Type where
     Yes : (prf : prop) -> Dec prop
     No  : (contra : prop -> Void) -> Dec prop

interface DecEq ty where
            decEq : (val1 : ty) -> (val2 : ty) -> Dec (val1 = val2)
-}

{- Redone example from 8.1 -}
exactLength : (len : Nat) -> (input : Vect m a) -> Maybe (Vect len a)
exactLength {m} len input = case decEq m len of
         Yes Refl => Just input
         No contra => Nothing

{- Just for Fun, This code shows code for instance of DecEq -}
data MyPair a b = MkMyPair a b

secondUnequal :  {a1 : a, a2 : a, b1 : b, b2 : b} -> (a1 = a2) -> (contra : (b1 = b2) -> Void) ->  (MkMyPair a1 b1 = MkMyPair a2 b2) -> Void
secondUnequal Refl contra Refl = contra Refl

{- Seems to know that it does not even need to check the second param! -}
firstUnequal : (contra : (a1 = a2) -> Void) -> (MkMyPair a1 b1 = MkMyPair a2 b2) -> Void
firstUnequal contra Refl = contra Refl

(DecEq a, DecEq b) => DecEq (MyPair a b) where
   decEq (MkMyPair a1 b1) (MkMyPair a2 b2) = case decEq a1 a2 of 
        Yes Refl => case decEq b1 b2 of
            Yes Refl => Yes Refl
            No contra => No (secondUnequal Refl contra)
        No contra => No (firstUnequal contra)
