|Markdown version of this file: https://github.com/rpeszek/IdrisTddNotes/wiki/idrVsHs_Part2_Sec8_2_5
|Idris Src: Sec8_2_5.idr

Section 8.2.5 Nat `+` theorems in Vect append vs Haskell
======================================================
Both Idris and Haskell know that `2+3 = 3+2` because both sides evaluate to `5`.
But `n + m = m + n` is another story, this creates all these annoying compiler errors
like "Couldn't match type ‘1 + n’ with ‘n + 1’". 

This note focuses on a simple example of vector append. A more complex example of
`reverse : Vect n elem -> Vect n elem` will be handled separately and is a TODO.

Idris code example
------------------  
|IdrisRef: Sec8_2_5.idr 

Compared to Haskell
-------------------

> {-# LANGUAGE 
>     TypeOperators
>   , GADTs
>   , DataKinds
>   , AllowAmbiguousTypes
>   , RankNTypes
> #-}
> {-# OPTIONS_GHC -fwarn-incomplete-patterns #-}
>
> module Part2.Sec8_2_5 where
> import Util.NonLitsNatAndVector (Vect(..), Nat(..), SNat(..), type (+), SNatI, sNat)
> import Data.Type.Equality ((:~:)(Refl))
> import Part2.Sec8_1 (cong)
>
> myAppend :: forall n m a. Vect n a -> Vect m a -> Vect (n + m) a
> myAppend Nil v2 = v2
> myAppend (x ::: xs) v2 = x ::: (myAppend xs v2)

I can do that easily enough:

> myAppend2 :: forall n m a. (n + m) ~ (m + n) => Vect n a -> Vect m a -> Vect (m + n) a
> myAppend2 = myAppend

or

> myAppend2Cheat :: Vect n a -> Vect m a -> Vect (m + n) a
> myAppend2Cheat = flip myAppend

but, defining myAppend2 recursively on its own is hard because type equality assumptions involve 
numbers other than `n` and `m` (`n` and `m` are hardwired in the type signature). 

Following the above Idris example works (with some trepidation and the need for redundant parameters):

> myAppend3 :: (forall mx a. SNat mx -> 'Z + mx :~: mx + 'Z) -> 
>              (forall left right a. SNat left -> SNat right -> (left + 'S right) :~: 'S (left + right)) -> 
>                 SNat n -> SNat m -> Vect n a -> Vect m a -> Vect (m + n) a
> myAppend3 prf0 _ _ m Nil v2 = case prf0 m of 
>        Refl -> v2
> myAppend3 prf0 prf1 (SS n) m (x ::: xs) v2 = let res = myAppend3 prf0 prf1 n m xs v2 
>     in case prf1 m n of
>        Refl -> x ::: res
>
> plusZeroRightNeutral :: SNat mx -> 'Z + mx :~: mx + 'Z
> plusZeroRightNeutral SZ     = Refl
> plusZeroRightNeutral (SS k) = cong (plusZeroRightNeutral k)
>
> plusSuccRightSucc :: SNat left -> SNat right -> (left + 'S right) :~: 'S (left + right)
> plusSuccRightSucc SZ right        = Refl
> plusSuccRightSucc (SS left) right = cong $ plusSuccRightSucc left right 
>
> {-| RankNTypes were not really needed other than for clarity -}
> myAppend3' :: SNat n -> SNat m -> Vect n a -> Vect m a -> Vect (m + n) a
> myAppend3' = myAppend3 plusZeroRightNeutral plusSuccRightSucc
> 
> test2 = myAppend2 ("1" ::: Nil) ("2" ::: Nil)
> test3' = myAppend3' (SS SZ) (SS SZ) ("1" ::: Nil) ("2" ::: Nil)
>
> {-| implicit version, SNatI n  is like SingI provides implicit evidence replacing SNat n -}
> myAppend3'' :: (SNatI n, SNatI m) => Vect n a -> Vect m a -> Vect (m + n) a
> myAppend3'' = myAppend3' sNat sNat 
>
> test3'' = myAppend3'' ("1" ::: Nil) ("2" ::: Nil)


ghci:
```
*Part2.Sec8_2_5> test3'
"1" ::: ("2" ::: Nil)
*Part2.Sec8_2_5> test3''
"1" ::: ("2" ::: Nil)
```
Idris approach with `rewrite` is just much more expressive and simpler.
But, I like the implicit version `myAppend3''`.


Side Note about Haskell's `~` vs `:~:` GADT
-------------------------------------------
But this works:

> test1 :: forall n m a. (n + m) ~ (m + n) => Vect (n + m) a -> Vect (m + n) a
> test1 = id

This does not:
```
test0 :: forall n m a. (n + m :~: m + n) -> Vect (n + m) a -> Vect (m + n) a
test0 _ = id
{-^ causes error: ‘+’ is a type function, and may not be injective, 
AllowAmbiguousTypes does not solve this issue -}
```
I do not fully understand why this is the case. (TODO)
