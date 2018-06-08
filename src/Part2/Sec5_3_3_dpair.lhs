|Markdown version of this file: https://github.com/rpeszek/IdrisTddNotes/wiki/Part2_Sec5_3_3_dpair
|Idris Src: Sec5_3_3_dpair.idr

Section 5.3.3. Dependent Pair vs Haskell
========================================

Idris code example
------------------  
|IdrisRef: Sec5_3_3_dpair.idr 

Compared to Haskell
-------------------
Note, standard approach in Haskell is to use existential type (or GADT which gives
equivalent functionality).  Typical name used in Haskell for this starts with 'Some'
 
This follows the idea from 5.3.2 and naming convention from the book so instead of
`SomeVect` I have `VectUnknown`

> {-# LANGUAGE DeriveFunctor
>    , StandaloneDeriving
>    , GADTs
>    , KindSignatures
>    , DataKinds
>    , TypeOperators 
>    , ScopedTypeVariables
>    , RankNTypes
> #-}
> {-# OPTIONS_GHC -fwarn-incomplete-patterns #-}
> {-# OPTIONS_GHC -fwarn-unused-imports #-}
>
> module Part2.Sec5_3_3_dpair where
> import GHC.TypeLits
> import Part2.Sec3_2_3_gen (Vect(..))
>
> {-| 
>  Provides link between Nat types and values. Often called Natty ('singletons' also calls it 'Sing n'.
>  SNat allows to lift from value n to type n. And provides run time reflexion.
>  Note: using predecessor (n - 1) instead of (1 + n) seems, in some cases, 
>  to work better see Part2.Sec6_2_1_adder 
> -}
> data SNat (n :: Nat) where
>  SZ :: SNat 0
>  SS :: SNat n -> SNat (1 + n)
>
> deriving instance Show (SNat n) 
>
> {-| In Haskell, this would be typically called SomeVect -}
> data VectUnknown a where 
>    MkVect :: SNat n -> Vect n a -> VectUnknown a 
>  
> deriving instance Show a => Show (VectUnknown a) 
>
> listToVect :: [a] -> VectUnknown a
> listToVect [] = MkVect SZ VNil
> listToVect (x : xs) = 
>              let forXs = listToVect xs
>              in case forXs of
>              MkVect nx forXsV -> MkVect (SS nx) (x ::: forXsV) 

ghci:
```
*Part2.Sec5_3_3_dpair> listToVect [1,2,3]
MkVect (SS (SS (SS SZ))) (1 ::: (2 ::: (3 ::: VNil)))
*Part2.Sec5_3_3_dpair> 
```
There is also a CPS approach, `singletons` library uses it, (it uses `RankNTypes`).
For `Vect` type I can define:

> withVectUnknown :: VectUnknown a -> (forall n . SNat n -> Vect n a -> r) -> r
> withVectUnknown (MkVect n v) f = f n v
>
> withListAsVect :: [a] -> (forall n . SNat n -> Vect n a -> r) -> r 
> withListAsVect list f = withVectUnknown (listToVect list) f
>
> test = withListAsVect [1,2,3] $ \n vect -> show vect

This is similar to `withNat`, `withSomeNat` in 
[/src/Util/NonLitsNatAndVector.hs](../blob/master/src/Data/CodedByHand/Nat.hs)  

ghci:
```
*Part2.Sec5_3_3_dpair> test
"1 ::: (2 ::: (3 ::: VNil))"
```
