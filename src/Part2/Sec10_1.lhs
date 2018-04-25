|Markdown version of this file: https://github.com/rpeszek/IdrisTddNotes/wiki/idrVsHs_Part2_Sec10_1
|Idris Src: Sec10_1.idr

Section 10.1 Idris `ListLast` and `SplitList` views vs Haskell
==============================================================

Idris code example
------------------  
|IdrisRef: Sec10_1.idr 

Compared to Haskell
-------------------

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
> module Part2.Sec10_1 where
> import Util.SingVector
> import Util.SingList
> import Part2.Sec9_1
> import Part2.Sec9_2
> import Data.Singletons
> import Data.Singletons.TH

`describeList` example
----------------------

> data ListLast  (xs :: List a) where 
>    Empty :: ListLast 'LNil 
>    NonEmpty :: forall (xs :: List a) (x :: a). Sing xs -> Sing x -> ListLast (Append xs (OneElem x))
> 
> listLast :: forall (xs :: List a) . Sing xs -> ListLast xs
> listLast SLNil = Empty
> listLast (x `SLCons` xs) = case listLast xs of
>       Empty -> NonEmpty SLNil x
>       NonEmpty ys y -> NonEmpty (SLCons x ys) y
>
> describeHelper1 :: forall (input :: List a) . (SingKind a, Show (Demote a)) => Sing input -> ListLast input -> String
> describeHelper1 SLNil Empty = "Empty"
> describeHelper1 _ (NonEmpty xs x) = "Non-empty, initial portion = " ++ (show $ fromSing xs)
> 
> describeHelper2 :: forall (xs :: List a) . (SingKind a, Show (Demote a)) => Sing xs -> String
> describeHelper2 xs = describeHelper1 xs (listLast xs)
> 
> describeListEnd :: (SingKind a, Show (Demote a)) => List (Demote a) -> String
> describeListEnd list = withSomeSing list describeHelper2

Int does not have the boilerplate needed by `singletons`, I use `Nat` to test it

> test :: List Nat
> test =  Z `LCons` ((S Z) `LCons` LNil)
> 
> describeListNat :: List Nat -> String
> describeListNat = describeListEnd

ghci
```
*Part2.Sec10_1> describeListEnd test
"Non-empty, initial portion = LCons Z LNil"
```

Slow `reverse` example
----------------------

> myReverseHelper :: forall (xs :: List a) . ListLast xs -> Sing xs -> SomeSing (List a)
> myReverseHelper Empty _ = SomeSing SLNil 
> myReverseHelper (NonEmpty xs x) _ = SomeSing $ SLCons x xs 
> 
> myReverse :: (SingKind a) => List (Demote a) -> List (Demote a)
> myReverse list = case withSomeSing list (\xs ->  myReverseHelper (listLast xs) xs) of 
>                    SomeSing res -> fromSing res

ghci
```
*Part2.Sec10_1> myReverse test
LCons (S Z) (LCons Z LNil)
```

Initially, I tried to implement myReverse using 
```
appendTh :: Sing xs -> Sing x -> ('LCons x xs :~: Append xs (OneElem x))
myReverseHelper :: forall (xs :: List a) . Sing xs -> ListLast xs -> Sing xs
```
but it did not seemed right and was it was hard/impossible go far with it. 
`SomeSing (List a)` made things workable.

`mergeSort` example
-------------------

TODO

Exercises
---------

TODO
