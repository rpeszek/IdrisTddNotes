|Markdown version of this file: https://github.com/rpeszek/IdrisTddNotes/wiki/Part2_Sec8_2_5_vappd
|Idris Src: Sec8_2_5_vappd.idr

Section 8.2.5 Nat `+` theorems in Vect append vs Haskell
========================================================

Both Idris and Haskell know that `2+3 = 3+2` because both sides evaluate to `5`.
But `n + m = m + n` is another story, this creates all these annoying compiler errors
like "Couldn't match type ‘1 + n’ with ‘n + 1’". 

Idris code example
------------------  
|IdrisRef: Sec8_2_5_vappd.idr 

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
> {-# OPTIONS_GHC -fwarn-unused-imports #-}
>
> module Part2.Sec8_2_5_vappd where
> import Data.CodedByHand (Vect(..), Nat(..), SNat(..), type (+), SNatI, sNat, SomeVect(..))
> import qualified Data.CodedByHand as V
> import Data.Type.Equality ((:~:)(Refl), sym)
> import Part2.Sec8_1_eqproof (cong)
>
> {- convenience function that allows to use weaker typed lists to test the work -}
> testAppend :: [a] -> [a] -> (forall n m. Vect n a -> Vect m a -> Vect (m + n) a) -> SomeVect a
> testAppend xs ys fapp = V.listWithVect xs (\vxs -> V.listWithVect ys (\vys -> SomeVect $ fapp vxs vys))
>
> myAppend :: forall n m a. Vect n a -> Vect m a -> Vect (n + m) a
> myAppend VNil v2 = v2
> myAppend (x ::: xs) v2 = x ::: (myAppend xs v2)

I can do that easily enough

> myAppend2 :: forall n m a. (n + m) ~ (m + n) => Vect n a -> Vect m a -> Vect (m + n) a
> myAppend2 = myAppend

but this introduces the `(n + m) ~ (m + n)` constraint that is hard to work with, for example, 
`testAppend [1,2] [6] myAppend2` has no chance of compiling and all the nice 
infrastructure build around existential (`SomeVect`) or rank2 quantification (`listWithVect`) will not 
compile with it.

Or I can just do this:

> myAppend2Cheat :: Vect n a -> Vect m a -> Vect (m + n) a
> myAppend2Cheat = flip myAppend

The best approach seems to use `:~:` mimicking Idris.

> myAppend3 :: SNat n -> SNat m -> Vect n a -> Vect m a -> Vect (m + n) a
> myAppend3 n m = case plusCommutative n m of Refl -> myAppend 
> myAppend3' :: (SNatI n, SNatI m) => Vect n a -> Vect m a -> Vect (m + n) a
> myAppend3' = myAppend3 sNat sNat 
> myAppend3'' :: Vect n a -> Vect m a -> Vect (m + n) a
> myAppend3'' v1 v2 = myAppend3 (V.vlength v1) (V.vlength v2) v1 v2
>
> -- note: plusZeroRightNeutral, plusSuccRightSucc are reversed compared to Idris
> plusCommutative :: SNat left -> SNat right -> ((left + right) :~: (right + left))
> plusCommutative SZ right = plusZeroRightNeutral right
> plusCommutative (SS k) right = case plusCommutative k right of Refl -> sym (plusSuccRightSucc right k)

Defining the flipped myAppend recursively on its own is harder because type equality assumptions involve 
numbers other than `n` and `m` (`n` and `m` are hardwired in the type signature). 

Following the above Idris example to just fix the original `myAppend1` implementation
checks out:

> myAppend4 :: SNat n -> SNat m -> Vect n a -> Vect m a -> Vect (m + n) a
> -- myAppend4' = myAppend4 plusZeroRightNeutral plusSuccRightSucc
> myAppend4 _ m VNil v2 = case plusZeroRightNeutral m of 
>        Refl -> v2
> myAppend4 (SS n) m (x ::: xs) v2 = let res = myAppend4 n m xs v2 
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

Side-note I find using `cong` to be more intuitive but is not needed:

> plusZeroRightNeutral' :: SNat mx -> 'Z + mx :~: mx + 'Z
> plusZeroRightNeutral' SZ     = Refl
> plusZeroRightNeutral' (SS k) = case plusZeroRightNeutral' k of Refl -> Refl
>
> plusSuccRightSucc' :: SNat left -> SNat right -> (left + 'S right) :~: 'S (left + right)
> plusSuccRightSucc' SZ right        = Refl
> plusSuccRightSucc' (SS left) right = case plusSuccRightSucc left right of Refl -> Refl

(end of side-note)
 
> test2 = myAppend2 ("1" ::: "2" ::: VNil) ("3" ::: VNil)
> test4 = myAppend4 (SS (SS SZ)) (SS SZ) ("1" ::: "2" ::: VNil) ("3" ::: VNil)
>
> {-| implicit version, SNatI n  is like SingI provides implicit evidence replacing SNat n -}
> myAppend4' :: (SNatI n, SNatI m) => Vect n a -> Vect m a -> Vect (m + n) a
> myAppend4' = myAppend4 sNat sNat 
>
> test4' = myAppend4' ("1" ::: "2" ::: VNil) ("3" ::: VNil)
>
> myAppend4'' ::  Vect n a -> Vect m a -> Vect (m + n) a
> myAppend4'' v1 v2 = myAppend4 (V.vlength v1) (V.vlength v2) v1 v2
>
> test4'' = myAppend4'' ("1" ::: "2" ::: VNil) ("3" ::: VNil)


ghci:
```
*Part2.Sec8_2_5_vappd> test2
"1" ::: ("2" ::: ("3" ::: VNil))
*Part2.Sec8_2_5_vappd> test4
"1" ::: ("2" ::: ("3" ::: VNil))
*Part2.Sec8_2_5_vappd> test4'
"1" ::: ("2" ::: ("3" ::: VNil))
*Part2.Sec8_2_5_vappd> test4''
"1" ::: ("2" ::: ("3" ::: VNil))
```
Here is the runtime test that converts regular list and treats it as a vector:

ghci:
```
*Part2.Sec8_2_5_vappd> testAppend [1,2] [6] myAppend4''
SomeVect (1 ::: (2 ::: (6 ::: VNil)))
*Part2.Sec8_2_5_vappd> testAppend [1,2] [6] myAppend3''
SomeVect (1 ::: (2 ::: (6 ::: VNil)))
```
As could be expected the programmable `:~:` works great!  
Idris approach with `rewrite` is feels more expressive and simpler.
