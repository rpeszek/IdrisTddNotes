|Markdown version of this file: https://github.com/rpeszek/IdrisTddNotes/wiki/idrVsHs_Part2_Sec8_2
|Idris Src: Sec8_2_5.idr
|Idris Src: Sec8_2.idr

Section 8.2.5 Nat `+` theorems in Vect append vs Haskell
======================================================
Both Idris and Haskell know that `2+3 = 3+2` because both sides evaluate to `5`.
But `n + m = m + n` is another story, this creates all these annoying compiler errors
like "Couldn't match type ‘1 + n’ with ‘n + 1’". 

This note focuses on a simple example of vector append. A more complex example of
`reverse : Vect n elem -> Vect n elem` is in 
[/src/Part2/Sec8_2.idr](../blob/master/src/Part2/Sec8_2.lhs) but I failed to go far 
mimicking that code in Haskell.

Idris code example
------------------  
|IdrisRef: Sec8_2_5.idr 

Compared to Haskell
-------------------
This code experiments with using Haskell's `~` type equality keyword. 
I added some notes about using `:~:` GADT as well. 

> {-# LANGUAGE 
>     TypeOperators
>   , GADTs
>   , DataKinds
>   , ScopedTypeVariables
>   , AllowAmbiguousTypes
> #-}
> {-# OPTIONS_GHC -fwarn-incomplete-patterns #-}
>
> module Part2.Sec8_2_5 where
> import Util.NonLitsNatAndVector
> import Data.Type.Equality

First some meaningless code
```
test0 :: forall n m a. (n + m :~: m + n) -> Vect (n + m) a -> Vect (m + n) a
test0 _ = id
{-^ causes error: ‘+’ is a type function, and may not be injective, 
AllowAmbiguousTypes does not solve this issue -}
```
But this works:

> test1 :: forall n m a. (n + m) ~ (m + n) => Vect (n + m) a -> Vect (m + n) a
> test1 = id

Now something more to the point

> myAppend :: forall n m a. Vect n a -> Vect m a -> Vect (n + m) a
> myAppend Nil v2 = v2
> myAppend (x ::: xs) v2 = x ::: (myAppend xs v2)

I can do that:

> myAppend2 :: forall n m a. (n + m) ~ (m + n) => Vect n a -> Vect m a -> Vect (m + n) a
> myAppend2 = myAppend

but defining myAppend2 recursively on its own is hard (I do not see how to do it) because type equality assumptions involve 
numbers other than `n` and `m` (`n` and `m` are hardwired in the type signature). 
The other issue here is that the constraint does not apply to the
recursive step so myAppend2 cannot be invoked recursively. (`(n + m) ~ (m + n), n ~ ('S n1)` does not imply 
`(n1 + m) ~ (m + n1)`). 
 
For example this attempt to make recursive call will not compile:
```
myAppend3 :: forall n m n1 a. 
                n + m :~: m + n -> 
                ((S n1) + m :~: m + (S n1) -> n1 + m :~: m + n1) -> 
                Vect n a -> Vect m a -> Vect (m + n) a
myAppend3 Refl _ Nil v2 = v2
myAppend3 prf impl (x ::: xs) v2 = let res = myAppend3 (impl prf) impl xs v2 
                                   in undefined
```
ghc error:
```
      Expected type: (n2 + m) :~: (m + n2)
        Actual type: (n1 + m) :~: (m + n1)
      NB: ‘+’ is a type function, and may not be injective
    • In the first argument of ‘myAppend3’, namely ‘(impl prf)’
```
Idris approach with `rewrite` is just much more expressive.
