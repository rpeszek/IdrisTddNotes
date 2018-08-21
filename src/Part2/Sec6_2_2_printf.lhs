|Markdown version of this file: https://github.com/rpeszek/IdrisTddNotes/wiki/Part2_Sec6_2_2_printf
|Idris Src: Sec6_2_2_printf.idr

Section 6.2.2. printf example vs Haskell
========================================
Type safe printf in Idris and Haskell.

Idris code example
------------------  
Idris repl:  

<img src="https://github.com/rpeszek/IdrisTddNotes/blob/master/image/Part2/Sec6_2_2.png" alt="/image/Part2/Sec6_2_2.png" width="550">

Code:

|IdrisRef: Sec6_2_2_printf.idr 

Here is the level to which Idris can generate some of this code:
```Idris
printfFmt1 : (fmt : Format) -> (acc : String) -> PrintfType fmt
printfFmt1 (Number x) acc = \i => ?printfFmt1_rhs_6
printfFmt1 (Str x) acc = \str => ?printfFmt1_rhs_5
printfFmt1 (Lit x y) acc = ?printfFmt1_rhs_7
printfFmt1 End acc = ?printfFmt1_rhs_4
```

Compared to Haskell
-------------------
Template Haskell/QuasiQuotation approach provides similar solution  
https://hackage.haskell.org/package/safe-printf#readme

I found a more dependently typed solution here (lacking the same string formatting as Idris):  
https://www.reddit.com/r/haskell/comments/55bvt4/typesafe_printf_with_typeintype/  
https://gist.github.com/gergoerdi/5a0785ae9366776ebd4f1090d75979d3  

This one is a classic:  
https://www.microsoft.com/en-us/research/publication/fun-type-functions/

See also discussion here:  
https://www.reddit.com/r/haskell/comments/41ek0f/idris_compile_checked_printf_possible_in_haskell/

It is not exactly the same thing but this library is neat:  
http://hackage.haskell.org/package/formatting

__Solution with some literal strings__

Trying to closely mimic Idris code does not go far because of how hard it is to work with type 
level strings. However the rest of the code is almost identical.

> {-# LANGUAGE  
>    TypeFamilies
>  , DataKinds
>  , GADTs
> #-}
> {-# OPTIONS_GHC -fwarn-incomplete-patterns #-}
> {-# OPTIONS_GHC -fwarn-unused-imports #-}
>
> module Part2.Sec6_2_2_printf where
> import GHC.TypeLits
> import Data.Kind (Type)
> import Data.Proxy
>
> data Format = Number Format
>             | Str Format
>             | Lit Symbol Format
>             | End
>
> {- ghc compiles this without ' ticks 
>   PrintfType maps Format to a plain type like Int -> String -> String -}
> type family PrintfType (fmt :: Format) :: Type where
>   PrintfType ('Number fmt) = Int -> PrintfType fmt
>   PrintfType ('Str fmt) = String -> PrintfType fmt
>   PrintfType ('Lit str fmt) = PrintfType fmt
>   PrintfType 'End = String
> 
> testFmt :: PrintfType ('Number ('Lit " greetings for " ('Str 'End)))
> testFmt = undefined

ghci:
```
*Part2.Sec6_2_2_printf> :t testFmt
testFmt :: Int -> String -> String
```

> {- PrintfType is 'polymorphic' (in Format kind) on RHS, this GADT is 'polymorphic' on LHS.
>    SFormat allows me to construct type safe printf expressions. 
>    GADT converts Format kind to Type -}
> data SFormat (fmt :: Format) where
>   SNum :: SFormat fmt -> SFormat ('Number fmt)
>   SStr :: SFormat fmt -> SFormat ('Str fmt)
>   SLit :: KnownSymbol str => Proxy str -> SFormat fmt -> SFormat ('Lit str fmt)
>   SEnd :: SFormat 'End
>
> {- Almost identical to Idris except GADT is used to convert Format DataKind -}
> printfFmt ::  SFormat fmt -> String -> PrintfType fmt
> printfFmt (SNum fmt) acc = \i -> printfFmt fmt (acc ++ show i)
> printfFmt (SStr fmt) acc = \str -> printfFmt fmt (acc ++ str)
> printfFmt (SLit p fmt) acc = printfFmt fmt (acc ++ (symbolVal p))
> printfFmt SEnd acc = acc
>
> testSFmt = SNum (SLit (Proxy :: Proxy " greetings for ") (SStr SEnd))
> testGreetings = printfFmt testSFmt "" -- "" is empty acc

ghci output:
```
*Part2.Sec6_2_2_printf> :t testSFmt
testSFmt :: SFormat ('Number ('Lit " greetings for " ('Str 'End)))
*Part2.Sec6_2_2_printf> :t testGreetings
testGreetings :: Int -> String -> String
*Part2.Sec6_2_2_printf> testGreetings 1000 "You"
"1000 greetings for You"
```
