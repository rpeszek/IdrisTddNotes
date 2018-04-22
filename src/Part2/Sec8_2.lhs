|Markdown version of this file: https://github.com/rpeszek/IdrisTddNotes/wiki/idrVsHs_Part2_Sec8_2
|Idris Src: Sec8_2.idr

Section 8.2 Vect reverse vs Haskell
===================================s
This is best read after the simpler [idrVsHs_Part2_Sec8_2_5](idrVsHs_Part2_Sec8_2_5).
It uses `plusZeroRightNeutral`, `plusSuccRightSucc` developed there.

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
> module Part2.Sec8_2 where
> import Util.NonLitsNatAndVector (Vect(..), Nat(..), SNat(..), type (+), FromTL, SNatI, sNat)
> import Data.Type.Equality ((:~:)(Refl))
> import Part2.Sec8_1 (cong)
> import Part2.Sec8_2_5 (plusZeroRightNeutral, plusSuccRightSucc)
>
> myReverse2 :: SNat n -> Vect n a -> Vect n a
> myReverse2 n xs = reverse' SZ n Nil xs
>   where reverse' :: SNat n -> SNat m -> Vect n a -> Vect m a -> Vect (n+m) a
>         reverse' n _ acc Nil = reverseLemma_nil n acc
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
> test = myReverse2 (SS (SS (SS SZ))) ("1" ::: "2" ::: "3 "::: Nil)
>
> {- implicit version, using SNatI n constraint instead of SNat n parameter -}
> myReverse2' :: SNatI n => Vect n a -> Vect n a
> myReverse2' = myReverse2 sNat
>
> test' = myReverse2' ("1" ::: "2" ::: "3 "::: Nil)

ghci
```
*Part2.Sec8_2> test
"3 " ::: ("2" ::: ("1" ::: Nil))
*Part2.Sec8_2> test'
"3 " ::: ("2" ::: ("1" ::: Nil))
```
