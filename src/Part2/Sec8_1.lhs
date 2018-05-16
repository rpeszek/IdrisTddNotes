|Markdown version of this file: https://github.com/rpeszek/IdrisTddNotes/wiki/idrVsHs_Part2_Sec8_1
|Idris Src: Sec8_1.idr

Section 8.1. Equality proofs vs Haskell
========================================
Dependent types are so rich that type checker needs help in figuring things out.
A proof of equality between natural numbers is needed to type check   
```
exactLength : (len : Nat) -> (input : Vect m a) -> Maybe (Vect len a)
```

Idris code example
------------------
The following code matches section 8.1 in the book.
`exactLength` is reimplemented in [idrVsHs_Part2_Sec8_3](idrVsHs_Part2_Sec8_3) using the `DecEq` interface.
  
|IdrisRef: Sec8_1.idr 


Compared to Haskell
-------------------
As before, I try to keep Haskell code very close to Idris. I am not using the `~` constraint. 
This code uses the explicit `:~:` type equality defined in `Data.Type.Equality` 
In the future, I may decide to play with this code using `~`.


> {-# LANGUAGE 
>    GADTs
>    , DataKinds
>    , TypeOperators
>    , TypeFamilies
>    , PolyKinds 
> #-}
> {-# OPTIONS_GHC -fwarn-incomplete-patterns #-}
>
> module Part2.Sec8_1 where
> import Data.CodedByHand (Vect(..), Nat(..), SNat(..), type (+), vlength)
> import Data.Type.Equality ((:~:)(Refl))
> 
> {- mimics concept of type level function in Idris-}
> type family F (a :: k1) :: k2 
>
> -- type family is a type level partial function so if x = y => f x = f y
> cong :: (x :~: y) -> F x :~: F y
> cong Refl = Refl 
> 
> checkEqNat :: SNat num1 -> SNat num2 -> Maybe (num1 :~: num2)
> checkEqNat SZ SZ = Just Refl
> checkEqNat SZ (SS k) = Nothing
> checkEqNat (SS k) (SZ) = Nothing
> checkEqNat (SS k) (SS j) = case checkEqNat k j of
>       Nothing -> Nothing
>       Just prf -> Just $ cong prf
> -- Note: SS :: SNat n -> SNat ('S n)
> type instance F n = 'S n
>
> {-| Note, GHC can figure out cong on its own -}
> checkEqNat' :: SNat num1 -> SNat num2 -> Maybe (num1 :~: num2)
> checkEqNat' SZ SZ = Just Refl
> checkEqNat' SZ (SS k) = Nothing
> checkEqNat' (SS k) (SZ) = Nothing
> checkEqNat' (SS k) (SS j) = case checkEqNat' k j of
>       Nothing -> Nothing
>       Just prf -> case prf of Refl -> Just Refl
> 
> exactLength :: SNat len -> Vect m a -> Maybe (Vect len a) 
> exactLength len vect = case checkEqNat (vlength vect) len of
>         Nothing -> Nothing
>         Just (Refl) -> Just vect
> 
> {- exercise examples -}
> {- 
>  type level partial application would be nice! 
>  would make F2 redundant 
> -}
> type family F2 (a :: k1) (b:: k2 ):: k3 
> 
> {- I need z in scope for this to work -}
> cong2 :: z -> (x :~: y) -> F2 z x :~: F2 z y
> cong2 _ Refl = Refl 
> 
> same_cons :: x -> xs :~: ys -> x ': xs :~: x ': ys
> same_cons x prf = cong2 x prf
> type instance F2 x xs = x ': xs
> 
> {-| cong-less version -}
> same_cons' :: x -> xs :~: ys -> x ': xs :~: x ': ys
> same_cons' x prf = case prf of Refl -> Refl
> 
> {- again need value of at least one type in scope -}
> same_lists :: x -> x :~: y -> xs :~: ys -> (x ': xs) :~: (y ': ys) 
> same_lists x Refl = same_cons x
> 
> data ThreeEqual a b c where
>   Refl3 :: ThreeEqual a a a
> 
> allSameS :: SNat x -> SNat y -> SNat z -> ThreeEqual x y z -> ThreeEqual ('S x) ('S y) ('S z)
> allSameS _ _ _ Refl3 = Refl3
> 
> {- It is good to have evidence of just one -}
> allSameS2 :: SNat x -> ThreeEqual x y z -> ThreeEqual ('S x) ('S y) ('S z)
> allSameS2 _ Refl3 = Refl3

Conclusions
-----------
Maybe this is just basics but Haskell typechecker is great.

__Why Proofs?__ 
The book presents the need for proofs as a natural consequence of using dependent types.
This makes a lot of sense to me. If a type parameter has some underlying requirements 
(e.g. `Vect` is parametrized by `n : Nat` which comes with an algebra), 
then it is only natural that the program will need to provide typechecker with some help 
(like `n + m = m + n`).
