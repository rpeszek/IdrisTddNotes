|Markdown version of this file: https://github.com/rpeszek/IdrisTddNotes/wiki/Part2_Sec3_2_3_gen
|Idris Src: Sec3_2_3_gen.idr

Section 3.2.3. Idris code synthesis example vs Haskell
======================================================

Idris code example
------------------  
|IdrisRef: Sec3_2_3_gen.idr   

Idris does not have a problem with generating map for Vector, but coding map for a List 
would require some manual work.

Type holes (for `mapV2`) provide information superior to what is available in ghci

idris repl
```
*src/Part2/Sec3_2_3_gen> :t mapV2_rhs_1
  b : Type
  a : Type
  f : a -> b
--------------------------------------
mapV2_rhs_1 : Vect 0 b
Holes: Part2.Sec3_2_3_gen.mapV2_rhs_2, Part2.Sec3_2_3_gen.mapV2_rhs_1
*src/Part2/Sec3_2_3_gen> :t mapV2_rhs_2
  b : Type
  a : Type
  f : a -> b
  x : a
  len : Nat
  xs : Vect len a
--------------------------------------
mapV2_rhs_2 : Vect (S len) b
Holes: Part2.Sec3_2_3_gen.mapV2_rhs_2, Part2.Sec3_2_3_gen.mapV2_rhs_1
```

Compared to Haskell
-------------------
__Automatic derivation DeriveFunctor, etc.__   
(This is not a fair comparison since Idris uses only type signature.)  
Surprisingly this ability goes beyond ADTs and Haskell can derive functor on simple GADTs like `Vect`:

> {-# LANGUAGE DeriveFunctor
>    , StandaloneDeriving
>    , GADTs
>    , KindSignatures
>    , DataKinds
>    , TypeOperators 
>    , ScopedTypeVariables
> #-}
> module Part2.Sec3_2_3_gen where
> import GHC.TypeLits
> 
> {- Note: using predecessor (n - 1) instead of (1 + n) seems, in some cases, 
> to work better see Part2.Sec6_2_1_adder -}
> data Vect (n::Nat) a where
>   VNil :: Vect 0 a
>   (:::) :: a -> Vect n a -> Vect (1 + n) a
> infixr 5 :::
> 
> testV :: Vect 3 Int
> testV = 1 ::: 2 ::: 3 ::: VNil
>                                 
> deriving instance Functor (Vect n)
> deriving instance Show a => Show (Vect n a) 

ghci:
```
*Part2.Temp2> fmap (+1) testV
2 ::: (3 ::: (4 ::: VNil))
*Part2.Temp2> fmap (*2) testV
2 ::: (4 ::: (6 ::: VNil))
```

and, obviously, I can just do

> data MyList a = Empty | Cons a (MyList a) deriving Functor

__Vs Hole Driven Development__  
This is somewhat more fair comparison since holes are based on type information only.
GHC 8.2.2 appears to provide much less info about `DataKinds` lifted types like Nat. 
If I type

```
mapV :: forall a b n. (a -> b) -> Vect n a -> Vect n b
mapV f VNil = _
```
I get 
```
   • Found hole: _ :: Vect n b
      Where: ‘n’ is a rigid type variable bound by
               the type signature for:
                 mapV :: forall a b (n :: Nat). (a -> b) -> Vect n a -> Vect n b
               at /Users/rpeszek/Documents/idris_play/IdrisTddNotes/src/Part2/Temp2.hs:24:
. . .
```
It would be nice if ghc told me that I need n=0, but it does not.

Adding 
```
mapV f (x ::: xs) = _ 
```
Is not very useful
```
   • Relevant bindings include
        xs :: Vect n1 a
          (bound at /Users/rpeszek/Documents/idris_play/IdrisTddNotes/src/Part2/Temp2.hs:26:15)
        x :: a
```
I am not told how `n1` is related to `n`.  
Similarly, I did not have much luck with 
```
mapV f (x ::: xs) = f x ::: _ 
```

I get better information if I mistype
```
mapV f (x ::: xs) = xs
``` 
```
    • Could not deduce: n1 ~ n
      from the context: n ~ (1 + n1)
```


Program synthesis. Some Relevant links.
--------------------------------------
Simple code generation for ADTs  
[Milewiski, CTFP](https://bartoszmilewski.com/2014/10/28/category-theory-for-programmers-the-preface/)  
[Ch.8 Functoriality](https://bartoszmilewski.com/2015/02/03/functoriality/).

More sophisticated synthesis approaches for code generation based on types (for future investigation) 
* djinn code synthesis offers often offers more than one solution (with limitations, e.g. allows no recursive types)
   - https://hackage.haskell.org/package/djinn
   - http://www.hedonisticlearning.com/djinn/
* justDoIt project 
   - https://www.joachim-breitner.de/blog/735-The_magic_%E2%80%9CJust_do_it%E2%80%9D_type_class
   - https://github.com/nomeata/ghc-justdoit
* exference project http://hackage.haskell.org/package/exference
* (scala) https://github.com/Chymyst/curryhoward
* (Idris) https://github.com/joom/hezarfen
* https://wiki.haskell.org/Applications_and_libraries/Theorem_provers

Other
* [Youtube (Scheme)](https://www.youtube.com/watch?v=OyfBQmvr2Hc) about code synthesis based on inputs and outputs 
