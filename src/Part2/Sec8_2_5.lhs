|Markdown version of this file: https://github.com/rpeszek/IdrisTddNotes/wiki/idrVsHs_Part2_Sec8_2_5
|Idris Src: Sec8_2_5.idr

Section 8.2.5 Nat `+` theorems in Vect append vs Haskell
========================================================

Both Idris and Haskell know that `2+3 = 3+2` because both sides evaluate to `5`.
But `n + m = m + n` is another story, this creates all these annoying compiler errors
like "Couldn't match type ‘1 + n’ with ‘n + 1’". 

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
> import Util.NonLitsNatAndVector (Vect(..), Nat(..), SNat(..), type (+), SNatI, sNat, listWithVect, SomeVect(..), vlength)
> import Data.Type.Equality ((:~:)(Refl), sym)
> import Part2.Sec8_1 (cong)
>
> myAppend :: forall n m a. Vect n a -> Vect m a -> Vect (n + m) a
> myAppend Nil v2 = v2
> myAppend (x ::: xs) v2 = x ::: (myAppend xs v2)

I can do that easily enough (but as we will see this does not work that well):

> myAppend2 :: forall n m a. (n + m) ~ (m + n) => Vect n a -> Vect m a -> Vect (m + n) a
> myAppend2 = myAppend

or

> myAppend2Cheat :: Vect n a -> Vect m a -> Vect (m + n) a
> myAppend2Cheat = flip myAppend

There is also a nice way to do use `:~:` instead of `~`. This approach relies on
some proofs that will be implemented later in this note

> myAppend2' :: SNat n -> SNat m -> Vect n a -> Vect m a -> Vect (m + n) a
> myAppend2' n m = case plusCommutative n m of Refl -> myAppend 
> myAppend2'' :: (SNatI n, SNatI m) => Vect n a -> Vect m a -> Vect (m + n) a
> myAppend2'' = myAppend2' sNat sNat 
> myAppend2''' :: Vect n a -> Vect m a -> Vect (m + n) a
> myAppend2''' v1 v2 = myAppend2' (vlength v1) (vlength v2) v1 v2
>
> -- note: plusZeroRightNeutral, plusSuccRightSucc are reversed compared to Idris
> plusCommutative :: SNat left -> SNat right -> ((left + right) :~: (right + left))
> plusCommutative SZ right = plusZeroRightNeutral right
> plusCommutative (SS k) right = case plusCommutative k right of Refl -> sym (plusSuccRightSucc right k)

Defining myAppend2 recursively on its own is hard because type equality assumptions involve 
numbers other than `n` and `m` (`n` and `m` are hardwired in the type signature). 

Following the above Idris example compiles:

> myAppend3 :: SNat n -> SNat m -> Vect n a -> Vect m a -> Vect (m + n) a
> -- myAppend3' = myAppend3 plusZeroRightNeutral plusSuccRightSucc
> myAppend3 _ m Nil v2 = case plusZeroRightNeutral m of 
>        Refl -> v2
> myAppend3 (SS n) m (x ::: xs) v2 = let res = myAppend3 n m xs v2 
>     in case plusSuccRightSucc m n of
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
> test2 = myAppend2 ("1" ::: "2" ::: Nil) ("3" ::: Nil)
> test3 = myAppend3 (SS (SS SZ)) (SS SZ) ("1" ::: "2" ::: Nil) ("3" ::: Nil)
>
> {-| implicit version, SNatI n  is like SingI provides implicit evidence replacing SNat n -}
> myAppend3' :: (SNatI n, SNatI m) => Vect n a -> Vect m a -> Vect (m + n) a
> myAppend3' = myAppend3 sNat sNat 
>
> test3' = myAppend3' ("1" ::: "2" ::: Nil) ("3" ::: Nil)
>
> myAppend3'' ::  Vect n a -> Vect m a -> Vect (m + n) a
> myAppend3'' v1 v2 = myAppend3 (vlength v1) (vlength v2) v1 v2
>
> test3'' = myAppend3'' ("1" ::: "2" ::: Nil) ("3" ::: Nil)


ghci:
```
*Part2.Sec8_2_5> test2
"1" ::: ("2" ::: ("3" ::: Nil))
*Part2.Sec8_2_5> test3
"1" ::: ("2" ::: ("3" ::: Nil))
*Part2.Sec8_2_5> test3'
"1" ::: ("2" ::: ("3" ::: Nil))
*Part2.Sec8_2_5> test3''
"1" ::: ("2" ::: ("3" ::: Nil))
```
Idris approach with `rewrite` is just much more expressive and simpler.
But, I like the implicit version `myAppend3''`.

So how does the runtime case pans out

> testAppend :: [a] -> [a] -> (forall n m. Vect n a -> Vect m a -> Vect (m + n) a) -> SomeVect a
> testAppend xs ys fapp = listWithVect xs (\vxs -> listWithVect ys (\vys -> SomeVect $ fapp vxs vys))

ghci:
```
*Part2.Sec8_2_5> testAppend [1,2] [6] myAppend2
<interactive>:9:22: error:
    • Couldn't match type ‘n + m’ with ‘m + n’
        arising from a use of ‘myAppend2’
      NB: ‘+’ is a type function, and may not be injective
```
That makes sense, `~` is not programatic and relies on type checker inferred type information.  
How about `:~:`?

ghci:
```
*Part2.Sec8_2_5> testAppend [1,2] [6] myAppend3''
SomeVect (1 ::: (2 ::: (6 ::: Nil)))
*Part2.Sec8_2_5> testAppend [1,2] [6] myAppend2'''
SomeVect (1 ::: (2 ::: (6 ::: Nil)))
```
As could be expected programmable `:~:` works!

Side Note about Haskell's `~` vs `:~:` GADT
-------------------------------------------
This works:

> test1 :: forall n m a. (n + m) ~ (m + n) => Vect (n + m) a -> Vect (m + n) a
> test1 = id

This does not:
```
test0 :: forall n m a. (n + m :~: m + n) -> Vect (n + m) a -> Vect (m + n) a
test0 _ = id
{-^ causes error: ‘+’ is a type function, and may not be injective, 
AllowAmbiguousTypes does not solve this issue -}
```
It kinda makes sense, in the second case we probably need a proof that
if `n1 :~: n2` then `Vect n1 a :~: Vect n2 b` (TODO)
