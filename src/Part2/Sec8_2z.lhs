|Markdown version of this file: https://github.com/rpeszek/IdrisTddNotes/wiki/idrVsHs_Part2_Sec8_2z
|Idris Src: Sec8_2.idr

Section 8.2 Vect reverse vs Haskell
===================================
This is best read after [idrVsHs_Part2_Sec8_2_5](idrVsHs_Part2_Sec8_2_5).
This note imports `plusZeroRightNeutral`, `plusSuccRightSucc`, `plusCommutative`, 
and `myAppend` from [idrVsHs_Part2_Sec8_2_5](idrVsHs_Part2_Sec8_2_5).

Idris code example
------------------  
|IdrisRef: Sec8_2.idr 

Compared to Haskell
-------------------
Haskell version is a straightforward copy of Idris code with exception of additional `SNat` parameter
which can be made implicit.

> {-# LANGUAGE 
>     TypeOperators
>   , GADTs
>   , DataKinds
> #-}
> {-# OPTIONS_GHC -fwarn-incomplete-patterns #-}
>
> module Part2.Sec8_2z where
> import Data.CodedByHand (Vect(..), Nat(..), SNat(..), type (+), FromTL, SNatI, sNat)
> import Data.Type.Equality ((:~:)(Refl))
> import Part2.Sec8_1 (cong)
> import Part2.Sec8_2_5 (plusZeroRightNeutral, plusSuccRightSucc, plusCommutative, myAppend)
>
> {- slow reverse -}
> myReverse :: SNat n -> Vect n elem -> Vect n elem
> myReverse _ VNil = VNil
> myReverse (SS n) (x ::: xs) = reverseLemma n ((myReverse n xs) `myAppend` (x ::: VNil) )
> 
> reverseLemma :: SNat k -> Vect (k + ('S 'Z)) elem -> Vect (S k) elem
> reverseLemma k result = case plusCommutative (SS SZ) k of
>          Refl -> result
> 
> myReverse' :: SNatI n => Vect n a -> Vect n a
> myReverse' = myReverse sNat

ghci:
```
*Part2.Sec8_2> myReverse (SS (SS (SS SZ))) ("1" ::: "2" ::: "3 "::: VNil)
"3 " ::: ("2" ::: ("1" ::: VNil))
*Part2.Sec8_2> myReverse' ("1" ::: "2" ::: "3 "::: VNil)
"3 " ::: ("2" ::: ("1" ::: VNil))
```

> myReverse2 :: SNat n -> Vect n a -> Vect n a
> myReverse2 n xs = reverse' SZ n VNil xs
>   where reverse' :: SNat n -> SNat m -> Vect n a -> Vect m a -> Vect (n+m) a
>         reverse' n _ acc VNil = reverseLemma_nil n acc
>         reverse' nacc (SS nxs) acc (x ::: xs)
>                       = reverseLemma_xs nacc nxs $ reverse' (SS nacc) nxs (x ::: acc) xs
>
> reverseLemma_nil :: SNat n -> Vect n a -> Vect (n + 'Z) a
> reverseLemma_nil n xs = case plusZeroRightNeutral n of
>         Refl -> xs
>
> reverseLemma_xs ::  SNat n1 -> SNat len -> Vect ((S n1) + len) a -> Vect (n1 + (S len)) a
> reverseLemma_xs n1 len xs = case plusSuccRightSucc n1 len of 
>                       Refl -> xs
>
> test = myReverse2 (SS (SS (SS SZ))) ("1" ::: "2" ::: "3 "::: VNil)
>
> {- implicit version, using SNatI n constraint instead of SNat n parameter -}
> myReverse2' :: SNatI n => Vect n a -> Vect n a
> myReverse2' = myReverse2 sNat
>
> test' = myReverse2' ("1" ::: "2" ::: "3 "::: VNil)

ghci
```
*Part2.Sec8_2> test
"3 " ::: ("2" ::: ("1" ::: VNil))
*Part2.Sec8_2> test'
"3 " ::: ("2" ::: ("1" ::: VNil))
```
