|Markdown version of this file: https://github.com/rpeszek/IdrisTddNotes/wiki/Play_ProofPerformance

In the past, I have lamented about increased computational complexity caused by proofs. 
This note puts these lamentations to rest.   
Haskell code only, I am still not sure what is the preferred approach in Idris.
Based on the cost complexity claims in Sec 10_2 of the book, it appears Idris
handles it.
  
> {-# LANGUAGE 
>     TypeOperators
>   , DataKinds
>   , TypeFamilies
>   , PolyKinds
> #-}
> {-# OPTIONS_GHC -fenable-rewrite-rules #-}
>
> module Play.ProofPerformance where
> 
> import           Data.Type.Equality ((:~:)(Refl), sym)
> import           Unsafe.Coerce
> import qualified Test.QuickCheck as Property
> import           Data.Singletons
> import           Debug.Trace
> import           Data.SingBased.NatTheorems (plusCommutative)
> import           Data.SingBased.Nat

This note shows how to deal with computational cost of proofs using `plusCommutative`
as example.  I show several approaches.  
Instead of creating proof from scratch I use the imported implementation and 
just rename it adding a number suffix.
 
`plusCommutative` proof is recursive, executing it at runtime would add 
unnecessary cost.
The proof program itself does not bring any value at run time. The only reason
for it is to provide evidence of type equality to the compiler.  
So why run it?  Termination concerns?  Runtime is not the time to discover
non-termination.  

Method 1
--------

> plusCommutative1 :: SNat left -> SNat right -> ((left + right) :~: (right + left))
> plusCommutative1 = traceShow "invoked" <$> plusCommutative
>
> test1 = plusCommutative1 s4 s1 

In his thesis and here 
https://typesandkinds.wordpress.com/2016/07/24/dependent-types-in-haskell-progress-report/
Richard Eisenberg suggests to do something along these lines:

> {-# NOINLINE plusCommutative1 #-}
> {-# RULES "proof" forall l r. plusCommutative1 l r = unsafeCoerce Refl #-} 

Here is a safer implementation of Eisenberg's suggestion 
(avoids runtime failures if `plusCommutative1`
is given wrong number of parameters in the `RULES` definition):

> plusCommutative1' :: SNat left -> SNat right -> ((left + right) :~: (right + left))
> plusCommutative1' = traceShow "invoked" <$> plusCommutative
>
> {-# NOINLINE plusCommutative1' #-}
> {-# RULES "proof" forall l r. plusCommutative1' l r = believeMeEq #-} 
> believeMeEq :: a :~: b 
> believeMeEq = unsafeCoerce Refl
>
> test1' = plusCommutative1' s4 s1 

A note of caution about experimenting with RULES using GHCI.  `-fenable-rewrite-rules`
is needed, also do not evaluate `plusCommutative1' s4 s1` directly as rewrite RULES
are not activated, evaluate `test1` -like values instead.

Method 2
--------

> plusCommutative2 :: SNat left -> SNat right -> ((left + right) :~: (right + left))
> plusCommutative2 = traceShow "invoked" <$> plusCommutative
>
> proveEqFast :: a :~: b ->  a :~: b
> proveEqFast _ = believeMeEq
>
> test2 = proveEqFast (plusCommutative s4 s1)

I think, I like this approach the best. 

Non termination
--------------

Anything can be proven using a non-terminating proof. Haskell does not check totality
but we could use QuickCheck to help!

> termProp :: (Integer, Integer) -> Bool
> termProp (i, j) = (integerToNat' i) `withSomeSing` (\ni -> 
>                  (integerToNat' j) `withSomeSing` (\nj -> 
>                    case plusCommutative ni nj of Refl -> True
>                    ))
>
> testTerm = Property.quickCheck termProp

This is obviously easier to do with Method 2, testing proof with rewrite rules 
seems pointless. 
