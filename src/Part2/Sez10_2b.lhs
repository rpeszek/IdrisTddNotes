|Markdown version of this file: https://github.com/rpeszek/IdrisTddNotes/wiki/idrVsHs_Part2_Sez10_2b
|Idris Src: Sez10_2b.idr

Sections 10.2.3 SnocList view and `isSuffix` function that uses multiple views 
==============================================================================

Idris code example
------------------  
|IdrisRef: Sez10_2b.idr 

Compared to Haskell
-------------------

> {-# LANGUAGE 
>    TypeOperators
>    , GADTs
>    , TypeFamilies
>    , DataKinds
>    , PolyKinds
>    , ScopedTypeVariables 
>    -- , KindSignatures
>    , FlexibleContexts
>    -- , FlexibleInstances
>    -- , TypeInType
> #-}
> {-# OPTIONS_GHC -fwarn-incomplete-patterns #-}
>
> module Part2.Sez10_2b where
> import Data.Type.Equality
> import Data.SingBased.Nat (Nat(..), type SNat, type Sing(..), integerToNat, natToInteger)
> import Data.SingBased.List (List(..), type Sing(..))
> import qualified Data.SingBased.List as L
> import Data.Singletons
> import Part2.Sez10_2a (SnocList(..), snocList)

I am taking a shortcut and use `Eq (Demote a)` (maybe not that bad?)

> isSuffixHelper :: forall (xs :: List a) (ys :: List a). (SingKind a, Eq (Demote a)) => 
>                     SnocList xs -> SnocList ys -> Bool
> isSuffixHelper Empty Empty = True
> isSuffixHelper Empty (Snoc _ _) = True
> isSuffixHelper (Snoc _ _) Empty = False
> isSuffixHelper (Snoc xs x) (Snoc ys y) 
>               = if fromSing x == fromSing y then isSuffixHelper xs ys else False 
>
> isSuffix :: (SingKind a, Eq (Demote a)) => List (Demote a) -> List (Demote a) -> Bool
> isSuffix list1 list2 
>     = withSomeSing list1 (\slist1 -> 
>         withSomeSing list2 (\slist2 ->  isSuffixHelper (snocList slist1) (snocList slist2))
>        )
>
> testIsSuffix list1 list2 = isSuffix 
>           (L.lToList . map integerToNat $ list1) 
>           (L.lToList . map integerToNat $ list2)

ghci:
```
*Part2.Sez10_2b> testIsSuffix [7,8,9,10] [1..10]
True
*Part2.Sez10_2b> testIsSuffix [7,8,9] [1..10]
False
```
