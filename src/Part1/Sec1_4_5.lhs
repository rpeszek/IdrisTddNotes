|Markdown version of this file: https://github.com/rpeszek/IdrisTddNotes/wiki/N_Part1_Sec1_4_5.md

Simple Idris example from 1.4.5 vs Haskell
------------------------------------------

__Idris code example__
|IdrisRef: Sec1_4_5.idr 

__Compared to Haskell__

> {-# LANGUAGE TypeFamilies
>  , DataKinds 
>  , KindSignatures 
>  , GADTs 
>  , ScopedTypeVariables
> #-}
> {-# OPTIONS_GHC -fwarn-incomplete-patterns #-}

> module Part1.Sec1_4_5 where
> import Data.Kind (Type)

Naive solution that tries to mimic Idris code is not type safe

> showInt :: Int -> String
> showInt = show
> 
> data StringOrInt1 = MkStr1 String | MkInt1 Int 
> 
> getStringOrInt1 :: Bool -> StringOrInt1
> getStringOrInt1 x = case x of
>           True -> MkInt1 10
>           False -> MkStr1 "Hello"
> 
> {-| Problem this compiles as well -}
> getStringOrInt1' :: Bool -> StringOrInt1
> getStringOrInt1' x = case x of
>            True -> MkStr1 "Hello"
>            False -> MkInt1 10
> 
> {-| Problem this does not depend on first param -}
> valToString1 :: Bool -> StringOrInt1 -> String
> valToString1 _ val = case val of
>          MkInt1 x -> showInt x
>          MkStr1 x -> x


Using Type Families, GADTs, and DataKinds provides good (almost equivalent with some differences) type safety but
the boiler plate is big and conceptual difficulty is significantly higher

> data StringOrInt2 a where
>     MkStr2 :: String -> StringOrInt2 String
>     MkInt2 :: Int -> StringOrInt2 Int
> 
> extractStr :: StringOrInt2 String -> String
> extractStr (MkStr2 s) = s
> 
> extractInt :: StringOrInt2 Int -> Int 
> extractInt (MkInt2 i) = i
> 
> type family StrOrIntF (x::Bool) :: Type where
>    StrOrIntF 'True = Int 
>    StrOrIntF 'False = String 
> 
> data SBool (b :: Bool) where 
>    STrue :: SBool True
>    SFalse :: SBool False
> 
> getStringOrInt2 :: forall (a :: Bool). SBool a -> StringOrInt2 (StrOrIntF a)
> getStringOrInt2 x = case x of
>           STrue -> MkInt2 10
>           SFalse -> MkStr2 "Hello"
> 
> {-! This compiles with warn-incomplete-patterns, sweet!!! -}
> valToString2 :: forall (a :: Bool). SBool a -> StringOrInt2 (StrOrIntF a) -> String
> valToString2 x val = case x of
>           STrue -> showInt $ extractInt val
>           SFalse -> extractStr val
> 
> {-| However this still compiles which seems bad but see testGood below -}
> valToString2' :: forall (a :: Bool). SBool a -> StringOrInt2 (StrOrIntF a) -> String
> valToString2' _ val = case val of
>          MkInt2 x -> showInt x
>          MkStr2 x -> x
> 
> testGood = valToString2' SFalse (MkStr2 "Test")

This no longer builds. Good!:
```
getStringOrInt2' :: forall (a :: Bool). SBool a -> StringOrInt2 (StrOrIntF a)
getStringOrInt2' x = case x of
          STrue -> MkStr2 "Hello"
          SFalse -> MkInt2 10
```
Neither does this:
```
testBad = valToString2' STrue (MkStr2 "Test")
```


Conclusions
-----------
Idris dependent types are NICE!!! 
This type of code is much simpler and has much less boiler plate in Idris compared to Haskell.

