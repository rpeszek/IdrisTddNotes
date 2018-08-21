|Markdown version of this file: https://github.com/rpeszek/IdrisTddNotes/wiki/Part2_Sez10_1_views
|Idris Src: Sez10_1_views.idr 
 
_using 'z' in the name to recover alphabetical sort of sections_

Section 10.1 Idris `ListLast`, `SplitList`, `TakeN` views vs Haskell
====================================================================

__Pattern matching using views.__  Idris allows for a very expressive pattern match 
informed by GADT-like structures.  
Haskell does not and the GADTs need to be used directly in the pattern match.
Well, there is the `ViewPatterns` pragma, which I am using here, but I am not
very happy about it (see Slow `reverse` example below).
Also, Haskell GADTs need to contain more information, while Idris can infer 
(or, rather, _exfer_) such information.  
Idris is capable of matching on the type (RHS) of constructor.  
This extends the traditional matching on the constructor itself (LHS).
 
I ended up using `SomeSing` in the return type and I am testing with `Nat` data trying
to avoid complexity of using literals in dependently typed Haskell code.
My Haskell examples use `singletons`.

Idris code example
------------------  
|IdrisRef: Sez10_1_views.idr 

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
>    , ViewPatterns
> #-}
> {-# OPTIONS_GHC -fwarn-incomplete-patterns #-}
> {-# OPTIONS_GHC -fwarn-unused-imports #-}
>
> module Part2.Sez10_1_views where
> import Data.SingBased.Nat (Nat(..), type Sing(..), integerToNat, natToInteger, sHalf)
> import Data.SingBased.List (List(..), type Sing(..))
> import qualified Data.SingBased.List as L
> import qualified Part2.Sec8_3_deceq as P
> import Data.Singletons
> import Data.Bifunctor (bimap)

`describeList` example
----------------------

> data ListLast  (xs :: List a) where 
>    Empty :: ListLast 'LNil 
>    NonEmpty :: forall (xs :: List a) (x :: a). 
>                Sing xs -> Sing x -> ListLast (L.Append xs (L.OneElem x))
> 
> listLast :: forall (xs :: List a) . Sing xs -> ListLast xs
> listLast SLNil = Empty
> listLast (x `SLCons` xs) = case listLast xs of
>       Empty -> NonEmpty SLNil x
>       NonEmpty ys y -> NonEmpty (SLCons x ys) y
>
> describeHelper1 :: forall (input :: List a) . (SingKind a, Show (Demote a)) => 
>                     Sing input -> ListLast input -> String
> describeHelper1 SLNil Empty = "Empty"
> describeHelper1 _ (NonEmpty xs x) = "Non-empty, initial portion = " ++ (show $ fromSing xs)
> 
> describeHelper2 :: forall (xs :: List a) . (SingKind a, Show (Demote a)) => 
>                     Sing xs -> String
> describeHelper2 xs = describeHelper1 xs (listLast xs)
> 
> describeListEnd :: (SingKind a, Show (Demote a)) => List (Demote a) -> String
> describeListEnd list = withSomeSing list describeHelper2

Int does not have the boilerplate needed by `singletons`, I use `Nat` to test it

> test :: List Nat
> test =  Z `LCons` (S Z) `LCons` LNil
> 
> describeListNat :: List Nat -> String
> describeListNat = describeListEnd

ghci
```
*Part2.Sez10_1_views> describeListEnd test
"Non-empty, initial portion = LCons Z LNil"
```

Slow `reverse` example
----------------------

I am also using `ViewPatterns` here (see `myReverseHelper` `listLast -> ...` syntax).  
I am not using them elsewhere. 
It appears that with GHC 8.2.2 this extension does not play well with 
`-fwarn-incomplete-patterns`. 

> myReverseHelper :: forall (xs :: List a) . Sing xs  -> SomeSing (List a)
> myReverseHelper (listLast -> Empty) = SomeSing SLNil 
> myReverseHelper (listLast -> (NonEmpty xs x)) = case myReverseHelper xs of
>              SomeSing sres -> SomeSing $ SLCons x sres 
> myReverseHelper _ = error "ViewPatterns do not know that pattern match is exhaustive" 
> 
> myReverse :: (SingKind a) => List (Demote a) -> List (Demote a)
> myReverse list = case withSomeSing list (\xs ->  myReverseHelper xs) of 
>                    SomeSing res -> fromSing res
>
> testWithList :: [a] -> (a->b) -> (List b -> List c) -> (c->d) -> [d]
> testWithList al fab flist fcd 
>        = map fcd $ L.listToL $ flist $ L.lToList (map fab al)

ghci
```
*Part2.Sez10_1_views> testWithList [4,2,7,1] integerToNat myReverse natToInteger
[1,7,2,4]
```

Note, I have to use `SomeSing (List a)` as return type when defining 
`myReverseHelper` or similar type level list operations. Returning `Sing xs` would
imply that the returned list is exactly the same as `Sing xs` input.  
For example, this works 

> myTail :: forall (xs :: List a) . Sing xs -> SomeSing (List a)
> myTail SLNil = SomeSing SLNil 
> myTail (SLCons x xs) = SomeSing xs

but this makes no sense and does not compile:
```
myTail :: forall (xs :: List a) . Sing xs -> Sing xs
myTail SLNil = SLNil 
myTail (SLCons x xs) = xs -- compilation problem
```


`mergeSort` example
-------------------

> data SplitList (xs :: List a) where
>     SplitNil :: SplitList 'LNil
>     SplitOne :: Sing x -> SplitList (L.OneElem x)
>     SplitPair :: forall (lefts :: List a) (rights :: List a). 
>                 Sing lefts -> Sing rights ->
>                 SplitList (L.Append lefts rights)
>
> -- used for testing only:
> testSplitList :: forall (xs :: List a). SingKind a => SplitList xs -> [List (Demote a)]
> testSplitList SplitNil = [LNil]
> testSplitList (SplitOne x) = [L.oneElem (fromSing x)]
> testSplitList (SplitPair xs ys) = [fromSing xs, fromSing ys]
>
> splitList :: forall (input :: List a). SingKind a => Sing input -> SplitList input
> splitList input = splitListHelp (fromSing input) input
>
> splitListHelp :: forall (input :: List a). SingKind a => 
>                   List (Demote a) -> Sing input -> SplitList input
> splitListHelp _ SLNil = SplitNil
> splitListHelp _ (SLCons x SLNil) = SplitOne x
> splitListHelp (_ `LCons` _ `LCons` counter) (item `SLCons` items) 
>       = case splitListHelp counter items of
>             SplitNil -> SplitOne item
>             SplitOne x ->  SplitPair (L.sOneElem item) (L.sOneElem x)
>             SplitPair lefts rights ->  SplitPair (item `SLCons` lefts) rights
> splitListHelp _ items = SplitPair SLNil items

ghci:
```
*Part2.Sez10_1_views> testSplitList $ splitList $ s0 `SLCons` s0 `SLCons` s1 `SLCons` s1 `SLCons` SLNil
[LCons Z (LCons Z LNil),LCons (S Z) (LCons (S Z) LNil)]
```

Unfortunately the standard `merge` function (see `Data.SingBased.List`) does not lift easily with `singletons`. 
SomeSing needs to be used in the result type to make it work

> sMerge :: forall (xs :: List a) (ys :: List a). (SingKind a, Ord (Demote a)) => 
>            Sing xs -> Sing ys -> SomeSing (List a)
> sMerge list1 list2 
>       = let xres = L.merge (fromSing list1) (fromSing list2)
>         in toSing xres

 
> mergeSort :: (SingKind a, Ord (Demote a)) => List (Demote a) -> List (Demote a)
> mergeSort list = case withSomeSing list (\xs -> mergeSortHelper (splitList xs) xs) of
>           SomeSing res -> fromSing res
>
> mergeSortHelper :: forall (xs :: List a). (SingKind a, Ord (Demote a)) => 
>                     SplitList xs -> Sing xs -> SomeSing (List a)
> mergeSortHelper SplitNil SLNil = SomeSing SLNil
> mergeSortHelper (SplitOne x) _ = SomeSing (L.sOneElem x)
> mergeSortHelper (SplitPair lefts rights) _ 
>     = case mergeSortHelper (splitList lefts) lefts of 
>         SomeSing leftsRes -> case mergeSortHelper (splitList rights) rights of
>           SomeSing rightsRes -> sMerge leftsRes rightsRes 
>
> testSort = testWithList [4,2,5,1] integerToNat mergeSort natToInteger

ghci
```
*Part2.Sez10_1_views> testSort
[1,2,4,5]
```

Exercises
---------

Definition identical to Idris is possible (requires `AllowAmbiguousTypes`):
```
data TakeN_ (xs :: List a) where
      Fewer_ :: TakeN_ xs
      Exact_ :: Sing n_xs -> TakeN_ (L.Append n_xs rest)
```
but it does not allow me to use:
```
takeN SZ _ = Exact
```
However, the following works:

> data TakeN (xs :: List a) where
>      Fewer :: TakeN xs
>      Exact :: forall (n_xs :: List a) (rest :: List a) (xs :: List a) . 
>                L.SList n_xs -> L.SList rest -> TakeN xs

The `forall (n_xs :: List a) (xs :: List a)` quantifications above are needed for the
expression `Exact (x `SLCons` rxs)` below to compile. 
I also need to maintain the `rest` argument in `Exact` constructor to get sufficient pattern match.
Also the above definition seems less type-safe (for example, `n_xs` does not need to be a sublist of `xs`).

> takeN :: forall (n :: Nat) (xs :: List a) . Sing n -> Sing xs -> TakeN xs
> takeN SZ xs = Exact SLNil xs
> takeN (SS k) SLNil = Fewer
> takeN (SS k) (x `SLCons` xs) = case takeN k xs of 
>       Fewer -> Fewer
>       Exact rxs rrest -> Exact (x `SLCons` rxs) rrest
>
> groupByNHelper :: forall (n :: Nat) (xs :: List a) . 
>                   Sing n -> 
>                   Sing xs -> SomeSing (List (List a))
> groupByNHelper n xs = case takeN n xs of 
>           Fewer -> SomeSing (L.sOneElem xs)
>           Exact n_xs rrest -> case groupByNHelper n rrest of
>                    SomeSing n_next -> SomeSing $ n_xs `SLCons` n_next
>
> groupByN :: (SingKind a) => Nat -> List (Demote a) -> List ( List (Demote a))
> groupByN n list = case withSomeSing n (\sn -> withSomeSing list $ groupByNHelper sn ) 
>       of SomeSing res -> fromSing res
>
> testGroup = testWithList [1..10] integerToNat (groupByN (integerToNat 3)) (map natToInteger . L.listToL) 

ghci:
```
*Part2.Sez10_1_views> testGroup
[[1,2,3],[4,5,6],[7,8,9],[10]]
```

> halvesHelper :: forall (xs :: List a) . Sing xs -> SomeSing (P.MyPair (List a) (List a))
> halvesHelper slist 
>        = case takeN (sHalf $ L.sLLength slist) slist of
>            Fewer -> SomeSing $ P.SMkMyPair slist SLNil
>            Exact xs ys -> SomeSing $ P.SMkMyPair xs ys
>
> halves :: (SingKind a) => List (Demote a) -> P.MyPair (List (Demote a)) (List (Demote a))
> halves list = case withSomeSing list halvesHelper of 
>        SomeSing res -> fromSing res
>
> testHalves =  let convert = map natToInteger . L.listToL
>               in bimap convert convert . halves . L.lToList . map integerToNat 

ghci:
```
*Part2.Sez10_1_views> testHalves [1..10]
MkMyPair [1,2,3,4,5] [6,7,8,9,10]
*Part2.Sez10_1_views> testHalves [1]
MkMyPair [] [1]
*Part2.Sez10_1_views> testHalves []
MkMyPair [] []
```
