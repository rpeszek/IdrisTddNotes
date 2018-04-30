|Markdown version of this file: https://github.com/rpeszek/IdrisTddNotes/wiki/idrVsHs_Part2_Sez10_2
|Idris Src: Sez10_2a.idr

Sections 10.2.1 - 10.2.2 SnocList view and fast reverse
=======================================================

Idris code example
------------------  
|IdrisRef: Sez10_2a.idr 

Compared to Haskell
-------------------

A straightforward conversion of Idris code has quadratic cost (Idris code has linear cost).

> {-# LANGUAGE 
>    TemplateHaskell
>    , TypeOperators
>    , GADTs
>    , TypeFamilies
>    , DataKinds
>    , PolyKinds
>    , KindSignatures
>    , EmptyCase
>    , RankNTypes
>    , LambdaCase
>    , ScopedTypeVariables 
>    , FlexibleContexts
> #-}
> {-# OPTIONS_GHC -fwarn-incomplete-patterns #-}
>
> module Part2.Sez10_2a where
> import Data.Type.Equality
> import Util.SingVector (Nat(..), type SNat, type Sing(..), integerToNat, natToInteger, sHalf)
> import Util.SingList (List(..), type Sing(..))
> import qualified Util.SingList as L
> import Data.Singletons
> import Part2.Sez10_1 (testWithList)
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
However `snocListHelp` `input` argument is no longer implicit and results in 
one `sAppend` call at each recursive step.
This is quadratic cost, ouch!  The only reason why we cary `input` around is to use it as an argument
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
*Part2.Sez10_2a> testWithList [4,2,7,1] integerToNat myReverse natToInteger
[1,7,2,4]
```
