|Markdown version of this file: https://github.com/rpeszek/IdrisTddNotes/wiki/idrVsHs_Part2_Sec6_2_1
|Idris Src: Sec6_2_1.idr

Section 6.2.1. adder example vs Haskell
=======================================
Type safe method with variable number of input params in Idris and Haskell.

Idris code example
------------------  
|IdrisRef: Sec6_2_1.idr 

Idris repl: 
 
<img src="https://github.com/rpeszek/IdrisTddNotes/blob/master/image/Part2/Sec6_2_1.png" alt="/image/Part2/Sec6_2_1.png" width="350">

Compared to Haskell
-------------------

> {-# LANGUAGE 
>      GADTs
>    , KindSignatures
>    , DataKinds
>    , TypeOperators 
>    , TypeFamilies
>    , StandaloneDeriving
>    , UndecidableInstances
> #-}
> {-# OPTIONS_GHC -fwarn-incomplete-patterns #-}
>
> module Part2.Sec6_2_1 where
> import Data.Kind (Type)
> import GHC.TypeLits
> import Data.Proxy
> -- import Part2.Sec5_3_3 (SNat(..))
> -- import Part2.Sec3_2_3 (Vect(..))

__GADT solution__  
This code is quite verbose and not very close to Idris.  Type Family solution 
gets much closer.

> data AdderGadt (n:: Nat) where
>    ZAdder :: Int -> AdderGadt 0
>    SAdder :: (Int -> AdderGadt (n - 1)) -> AdderGadt n
>
> instance Show (AdderGadt n) where
>    show (ZAdder i) = show i
>    show (SAdder f) = "Unresolved"
>
> createAdder :: SNat n -> Int -> AdderGadt n
> createAdder SZ acc = ZAdder acc
> createAdder (SS sn) acc = SAdder (\nextArg -> createAdder sn (nextArg + acc)) 
>
> resolveAdder ::  AdderGadt n -> Vect n Int -> Int 
> resolveAdder (ZAdder i) _ = i
> resolveAdder (SAdder f) (x ::: xs) = resolveAdder (f x) xs
> -- this condition should not be needed but
> -- GHC reports Pattern match(es) are non-exhaustive 
> resolveAdder (SAdder _) Nil = error "This should be impossible"
>
> {- Realigned SNat and Vect -}
>
> data SNat (n :: Nat) where
>  SZ :: SNat 0
>  SS :: SNat (n - 1) -> SNat n
>
> data Vect (n::Nat) a where
>   Nil :: Vect 0 a
>   (:::) :: a -> Vect (n - 1) a -> Vect n a
> infixr 5 :::
>
> sTwo = SS (SS SZ)
> test = resolveAdder (createAdder sTwo 0) (3 ::: 2 ::: Nil) 

this seems type safe and works. The error message on type mismatch is interesting:
```
*Part2.Sec6_2_1>  resolveAdder (createAdder sTwo 0) (3 ::: 2 ::: 1 ::: Nil) 
<interactive>:110:15: error:
    Variable not in scope:
      createAdder :: SNat 2 -> Integer -> AdderGadt 3
```

I am still using `GHC.TypeLits`. 
I had to realign Vec and SNat to be based on the predecessor `n - 1` instead of 
a successor `1 + n` or `n + 1` to avoid errors like the following (for `1 + n`)
```
 Could not deduce: n2 ~ n1
  from the context: n ~ (1 + n1)
```
These errors could be fixable, but using `n - 1' approach seems simpler.


__Type family solution (first attempt)__   
This code is almost exactly the same as Idris code:

> type family AdderType (n :: Nat) :: Type where
>   AdderType 0 = Int
>   AdderType n = Int -> AdderType (n - 1)

However attempting to compile this:
```
adder :: SNat n -> Int -> AdderType n
adder SZ acc = acc
adder (SS k) acc = \nextArg -> adder k (nextArg + acc)
```
result is compilation error (ghc 8.0.2)
```
• Couldn't match expected type ‘AdderType n’
                  with actual type ‘Int -> AdderType (n - 1)’
• The lambda expression ‘\ nextArg -> adder k (nextArg + acc)’
      has one argument,
      but its type ‘AdderType n’ has none
```

__Type family solution (working)__  
The problem seems to be again with `TypeLits`, this works just fine:

> data Nat' = Z' | S' Nat' 
> 
> data SNat' (n :: Nat') where
>   SZ' :: SNat' Z'
>   SS' :: SNat' n -> SNat' (S' n)
> 
> type family AdderType' (n :: Nat') :: Type where
>   AdderType' Z' = Int
>   AdderType' (S' n) = Int -> AdderType' n
> 
> adder' :: SNat' n -> Int -> AdderType' n
> adder' SZ' acc = acc
> adder' (SS' k) acc = \nextArg -> adder' k (nextArg + acc)
>
> sTwo' = SS' (SS' SZ')
> test' = adder' sTwo' 0 3 2

ghci output:
```
*Part2.Sec6_2_1> test'
5
*Part2.Sec6_2_1> adder sTwo' 0 3 2 1

<interactive>:132:1: error:
    • Couldn't match type ‘Int’ with ‘Integer -> t’
      Expected type: Int -> Int -> Integer -> t
        Actual type: AdderType' ('S' ('S' 'Z'))
    • The function ‘adder’ is applied to five arguments,
      but its type ‘SNat' ('S' ('S' 'Z'))
                    -> Int -> AdderType' ('S' ('S' 'Z'))’
      has only two
      In the expression: adder sTwo' 0 3 2 1
      In an equation for ‘it’: it = adder sTwo' 0 3 2 1
```

Conclusions
-----------
I am finding that using GHC.TypeLits Nat is a bit of a struggle.  I often get errors like 
Couldn't match type ‘n’ with ‘(n + 1) - 1’.  Using constraints like 
`n ~ ((n + 1) - 1)` does not always help. To move forward I created
Util.NonLitsNatAndVector.hs.

I like Idris more and more!
