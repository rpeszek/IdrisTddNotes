|Markdown version of this file: https://github.com/rpeszek/IdrisTddNotes/wiki/Part2_Sez10_2a_snoc
|Idris Src: Sez10_2a_snoc.idr

Sections 10.2.1 - 10.2.2 SnocList view and fast reverse
=======================================================

Idris code example
------------------  
|IdrisRef: Sez10_2a_snoc.idr 

Compared to Haskell
-------------------

A straightforward conversion of Idris code looks slower than Idris. 
Idris code has a linear cost ignoring the cost of proofs themselves.
Quoting the book: 
_"You now have an implementation of myReverse that runs in linear time, 
because it traverses the list once to build the SnocList view and then traverses 
the SnocList view once to build the reversed list."_  
It looks to me that, in Idris example (`snocListHelp`), we have a linear cost proof at each step 
causing overall quadratic cost.

> {-# LANGUAGE 
>    TypeOperators
>    , GADTs
>    , TypeFamilies
>    , DataKinds
>    , PolyKinds
>    , ScopedTypeVariables 
> #-}
> {-# OPTIONS_GHC -fwarn-incomplete-patterns #-}
> {-# OPTIONS_GHC -fwarn-unused-imports #-}
>
> module Part2.Sez10_2a_snoc where
> import Data.Type.Equality
> import Data.SingBased.Nat (type Sing(..))
> import Data.SingBased.List (List(..), type Sing(..))
> import qualified Data.SingBased.List as L
> import Data.Singletons
>
> data SnocList (xs :: List a) where
>    Empty :: SnocList 'LNil
>    Snoc :: forall (xs :: List a) (x :: a). 
>                  SnocList xs -> Sing x -> SnocList (L.Append xs (L.OneElem x))
>
> snocListHelp :: forall (input :: List a) (rest :: List a) . 
>                  Sing input ->  SnocList input -> Sing rest -> SnocList (L.Append input rest)
> snocListHelp input snoc SLNil = case sym (appendNilRightNeutral input) of Refl -> snoc
> snocListHelp input snoc (SLCons x xs) 
>       = case sym (appendAssociative input (L.sOneElem x) xs) of
>            Refl ->  snocListHelp (L.sAppend input (L.sOneElem x)) (Snoc snoc x) xs 

Similarly to Idris ghc needs `appendNilRightNeutral` and `appendAssociative` theorems to compile.
However `snocListHelp` `input` argument is no longer implicit `{input}` and results in 
one `sAppend` call at each recursive step.
This becomes quadratic complexity (even ignoring the cost of the proofs), ouch!  
The only reason why we cary `input` around is to use it as an argument
to proofs of `appendNilRightNeutral` and `appendAssociative`.
This is a type level aspect that Idris appears to handle without runtime cost!   
TODO - think about it more!

> appendNilRightNeutral :: forall (l :: List a) . Sing l -> L.Append l 'LNil :~: l
> appendNilRightNeutral SLNil = Refl
> appendNilRightNeutral (SLCons x xs) = case appendNilRightNeutral xs of Refl -> Refl
>
> appendAssociative ::  forall (l :: List a) (c :: List a) (r :: List a) .
>       Sing l -> Sing c -> Sing r -> L.Append l (L.Append c r) :~: L.Append (L.Append l c) r
> appendAssociative SLNil c r = Refl
> appendAssociative (SLCons x xs) c r = case appendAssociative xs c r of Refl -> Refl
>
> snocList :: forall (xs :: List a). Sing xs -> SnocList xs
> snocList xs = snocListHelp SLNil Empty xs
>
> myReverseHelper :: forall (l :: List a) . SnocList l -> SomeSing (List a)
> myReverseHelper Empty = SomeSing SLNil 
> myReverseHelper (Snoc sxs x) = case myReverseHelper sxs of
>         SomeSing l -> SomeSing $ SLCons x l 
>
> myReverseSing :: forall (l :: List a) . Sing l -> SomeSing (List a)
> myReverseSing = myReverseHelper . snocList 
>
> myReverse :: (SingKind a) => List (Demote a) -> List (Demote a)
> myReverse list = case withSomeSing list (\xs ->  myReverseSing xs) of 
>                    SomeSing res -> fromSing res


```
*Part2.Sez10_2a_snoc> testWithList [4,2,7,1] integerToNat myReverse natToInteger
[1,7,2,4]
```

I do not think the linear cost can be achieved by making the above `Sing input`
argument implicit (using constraint such as `SingI input`). 
The implicit `sing` will still be a reclusive call.

Reversing `Vect` 
----------------
I have implemented two versions of `myReverse` for `Vect`.
 
* [Part2.Sez10_2aVect.hs](../blob/master/src/Part2/Sez10_2aVect.hs)
* [Part2.Sez10_2aVect2.hs](../blob/master/src/Part2/Sez10_2aVect2.hs)

[Part2.Sez10_2aVect.hs](../blob/master/src/Part2/Sez10_2aVect.hs) approach mimics closely the list version above.   
The take away is:

* I had to use `:~~:` instead of `:~:` because ghc considered `appendNilRightNeutral`, `appendAssociative`
  equalities having different RHS and LHS kinds
* I had big hope that I will be able to replace `Sing list` evidence in `appendNilRightNeutral`, `appendAssociative` 
  with SNat` but I have failed. If that works my hope is to recover linear cost.

[Part2.Sez10_2aVect2.hs](../blob/master/src/Part2/Sez10_2aVect2.hs) is simpler and has linear cost (ignoring proofs)!
This is basically the same code as a straightforward implementation of `reverse` for `Vect` that uses 
accumulator, see 
[my presentation 1](https://github.com/rpeszek/presentations-code/blob/master/precise-types/src/Present/P5_VectRev1.hs)
and 
[my presentation 2](https://github.com/rpeszek/presentations-code/blob/master/precise-types/src/Present/P6_VectRev2.hs).

Compared to [Part2.Sez10_2aVect.hs](../blob/master/src/Part2/Sez10_2aVect.hs),
[Part2.Sez10_2aVect2.hs](../blob/master/src/Part2/Sez10_2aVect2.hs) is less a "type level" code.
It does not use `Sing vect` or `VAppend` type family.  The only proofs needed are about `Nat` and `+`.
