|Markdown version of this file: https://github.com/rpeszek/IdrisTddNotes/wiki/idrVsHs_Part2_Sec9_1
|Idris Src: Sec9_1.idr

Section 9.1 Type safe element of Vector vs Haskell
==================================================
This note is about type safe `elem` function and mimicking this in Haskell.

Idris code example
------------------  
|IdrisRef: Sec9_1.idr 

Compared to Haskell
-------------------
I am using only `Data.SingBased` moving forward. 

> {-# LANGUAGE 
>     TypeOperators
>   , GADTs
>   , TypeFamilies
>   , DataKinds
>   , PolyKinds
>   , ScopedTypeVariables
>   , StandaloneDeriving
>   , KindSignatures
>   , TypeInType
>   , AllowAmbiguousTypes
>   , EmptyCase
>   , UndecidableInstances 
>   , FlexibleContexts
> #-}
> {-# OPTIONS_GHC -fwarn-incomplete-patterns #-}
>
> module Part2.Sec9_1 where
> import Data.SingBased.Nat (Nat(..), type SNat, type Sing(..), s0, s1, s2, s3, type FromTL)
> import Data.SingBased.Vect (Vect(..), SVect(..), SomeKnownSizeVect(..))
> import Data.SingBased (someKnownSizeVectToVect, sVectToVect)
> import GHC.TypeLits hiding (Nat)
> import Data.Kind (Type)
> import Data.Void
> import Data.Type.Equality
> import Data.Singletons
> import Part2.Sec8_3 (Dec(..), DecEqSing(..), DecEq(..))

List `Elem`
----------

> data Elem (ax :: a) (bx :: [a]) where
>         Here :: Elem x (x ': xs)
>         There :: Elem x xs -> Elem x (y ': xs)
> deriving instance Show (Elem a b)
>
> oneInList :: Elem 1 (1 ': 2 ':3 ': '[])
> oneInList = Here
>
> threeInList :: Elem 3 '[1,2,3]
> threeInList = There (There Here)

This will not compile (good)
```
twoInList :: Elem 2 (1 ': 2 ':3 ': '[])
twoInList = Here
```
ghc error:
```
    • Couldn't match type ‘2’ with ‘1’
      Expected type: Elem 2 '[1, 2, 3]
        Actual type: Elem 2 '[2, 2, 3]

```

Vect `Elem`
----------

The same approach works for Vectors

> data VElem (ax :: a) (vx :: Vect k a) where
>         VHere :: VElem x (x '::: xs)
>         VThere :: VElem x xs -> VElem x (y '::: xs)
> deriving instance Show (VElem a b)
>
> twoInVect :: VElem 2 (1 '::: 2 '::: 3 '::: 'VNil)
> twoInVect = VThere VHere
>
> strInVect :: VElem "str" ("hello" '::: "str" '::: 'VNil)
> strInVect = VThere VHere

`Uninhabited`
-------------
`Data.Void` defines function `absurd :: Void -> a` which mimics `void` in Idris.
This shuffles things around to mimic Idris.

> void :: Void -> a
> void = absurd 
>
> class Uninhabited t where
>   uninhabited :: t -> Void
>
> {-| absurd' mimicking Idris -}
> absurd' :: Uninhabited t => t -> Void 
> absurd' = void . uninhabited

A type family version of this (which I need later)  
_TODO this needs more thinking_

> type family VoidF :: Void -> a
> type family UninhabitedF :: a -> Void


`removeElem` using `singletons`
------------------------------
This is very similar to Idris except the final result is demoted and `fwarn-incomplete-patterns` does not work so well.  
_Note, even using `TypeInType`, I was not able to auto-generate singletons for `Vect n a` itself._   
_I have implemented `SVect` by hand._  

> removeElemDem :: forall (n :: Nat) (val :: a) (xs :: Vect (S n) a) . SingKind a =>
>       SNat n -> Sing val ->  SVect xs -> VElem val xs -> Vect n (Demote a)
> removeElemDem _ val (_ `SCons` ys) VHere = sVectToVect ys
> removeElemDem (SS n1) val (y `SCons` ys) (VThere later) = (fromSing y) ::: (removeElemDem n1 val ys later)
> {- While Idris knows that the following case is invalid, 
>  GHC picks is up as error: Pattern match(es) are non-exhaustive
>  attempt to implement it as `absurd' later` causes compilation errors
> -}
> removeElemDem SZ val (SCons _ SNil) (VThere later) = undefined -- absurd' later
>
> testRemoveElemDem = removeElemDem s0 s3 (SCons s3 SNil) VHere

This version does not `Demote a` and is better and is closer to Idris:

> removeElem :: forall (n :: Nat) (val :: a) (xs :: Vect (S n) a) . SingKind a =>
>       SNat (S n) -> Sing val ->  SVect xs -> VElem val xs -> SomeKnownSizeVect n a
> removeElem (SS n) val (_ `SCons` ys) VHere = MkSomeKnownSizeVect n ys
> removeElem (SS (SS n)) val (y `SCons` ys) (VThere later) =
>       let res = removeElem (SS n) val ys later
>       in case res of 
>           MkSomeKnownSizeVect _ rys -> MkSomeKnownSizeVect (SS n) $ SCons y rys
> {- The absurd case remains, GHC does not know that we are dealing with one element list,
>   for example replacing `SCons _ _` with `SCons _ SNil` would cause Pattern match(es) are non-exhaustive
>   error
> -}
> removeElem (SS SZ) val (SCons _ _) (VThere _) = undefined -- absurd' later
>
> testRemoveElem = removeElem s1 s3 (SCons s3 SNil) VHere

ghci:
```
*Part2.Sec9_1> testRemoveElemDem
Nil
*Part2.Sec9_1> someKnownSizeVectToVect testRemoveElem
Nil
```
Nice!


`removeElem` using type families
------------------------------

I had somewhat less luck mimicking Idris's `removeElem` using type families

> type family RemoveElem (val :: a) (xs :: Vect (S n) a) (prf :: VElem val xs) :: Vect n a where
>   RemoveElem val (val '::: xs) 'VHere = xs
>   RemoveElem val (y '::: ys) ('VThere later) = y '::: RemoveElem val ys later

```
*Part2.Sec9_1> :kind! (RemoveElem "str" ("hello" '::: "str" '::: 'VNil) ('VThere 'VHere))
(RemoveElem "str" ("hello" '::: "str" '::: 'VNil) ('VThere 'VHere)) :: Vect
                                                                        ('S 'Z) Symbol
= "hello" '::: 'VNil

*Part2.Sec9_1> :kind! (RemoveElem "str1" ("hello" '::: "str" '::: 'VNil) ('VThere 'VHere))

<interactive>:1:52: error:
    • Expected kind ‘VElem "str1" ("hello" '::: ("str" '::: 'VNil))’,
        but ‘'VThere 'VHere’ has kind ‘VElem
                                         "str1" ("hello" '::: ("str1" '::: 'VNil))’
    • In the third argument of ‘RemoveElem’, namely
        ‘( 'VThere  'VHere)’
      In the type ‘(RemoveElem "str1" ("hello"
                                     ::: ("str" :::  'VNil)) ( 'VThere  'VHere))’
```
Good! 
 
The following code is not very useful (similarly to Idris `RemoveElem` is not resolved)

> data Test (a :: Vect ('S 'Z) Symbol) where
>    Test :: Test (RemoveElem "str" ("hello" '::: "str" '::: 'VNil) strInVect) 

`Test` compiles (because size is reduced by type family, but there is no evidence of type family actually working.

Unlike Idris, the following also compiles :( 

> data TestWrong (a :: Vect ('S 'Z) Symbol) where
>    TestWrong :: TestWrong (RemoveElem "str1" ("hello" '::: "str" '::: 'VNil) strInVect)  

TODO I need to study these limitations more.

Interestingly `RemoveElem` also complies when I include the absurd case! 

> type family RemoveElem' (val :: a) (xs :: Vect (S n) a) (prf :: VElem val xs) :: Vect n a where
>   RemoveElem' val (val '::: xs) 'VHere = xs
>   RemoveElem' val (y '::: 'VNil) ('VThere later) = VoidF (UninhabitedF later)
>   RemoveElem' val (y '::: ys) ('VThere later) = y '::: RemoveElem' val ys later
>

I can type the not logical case to invoke the uninhabited case for `RemoveElem'`
and the corresponding case is just not reduced for `RemoveElem`  
ghci:
```
*Part2.Sec9_1> :kind! (RemoveElem' "na" ("str" '::: 'VNil) ('VThere _))
(RemoveElem' "na" ("str" '::: 'VNil) ('VThere _)) :: Vect 'Z Symbol
= VoidF (UninhabitedF _)

*Part2.Sec9_1> :kind! (RemoveElem "na" ("str" '::: 'VNil) ('VThere _))
(RemoveElem "na" ("str" '::: 'VNil) ('VThere _)) :: Vect 'Z Symbol
= RemoveElem "na" ("str" '::: 'VNil) ('VThere _)
```
I cannot evaluate similar nonsense in Idris   
idris repl 
```
*Part2/Sec9_1> removeElem_auto "na" ["str"]
(input):1:1-28:When checking argument prf to function Part2.Sec9_1.removeElem_auto:
        Can't find a value of type 
                Elem "na" ["str"]
```

`isElem` example
----------------

The `notInNil` uses `EmptyCase` instead of the `impossible` Idris keyword

> notInNil :: VElem ax 'VNil -> Void
> notInNil x = case x of { }
>
> notInTail ::  (VElem ax xs -> Void) ->
>                    ((Sing ax :~: Sing x) -> Void) -> VElem ax (x '::: xs) -> Void
> notInTail notThere notHere VHere = notHere Refl
> notInTail notThere notHere (VThere later) = notThere later

The following, unfortunately, does not seem to work (TODO)

> isElem :: DecEq (Sing :: a -> Type) => Sing a -> SVect xs -> Dec (VElem a xs)
> isElem val SNil = No notInNil
> isElem val (SCons x xs) = undefined

use of `case decEq val x` or even `case decEq val val` on the RHS of the second case split
```
isElem val (SCons x xs) = case decEq val val of
        Yes Refl -> undefined 
        No notHere -> undefined
```
causes
```
ghc error:
   Could not deduce (DecEq Sing) arising from a use of ‘decEq’
      from the context: DecEq Sing  
```
But narrowing the scope to just `Nat` (from `Sing a` to `SNat n`) makes it work

> isElemNat :: SNat n -> SVect xs -> Dec (VElem n xs)
> isElemNat val SNil = No notInNil
> isElemNat val (SCons x xs) = case decEq val x of
>        Yes Refl -> Yes VHere
>        No notHere -> case isElemNat val xs of
>           Yes prf -> Yes (VThere prf)
>           No notThere -> No (notInTail notThere notHere)

ghci:
```
*Part2.Sec9_1> isElemNat s1 (SCons s1 SNil)
Yes
```
and the code is the same as in Idris.

I can also fix this using `DecEqSing`, which is probably closer to how I should code dependent types in Haskell 

> isElemSing :: DecEqSing k => forall n (a :: k) (xs :: Vect n k) . 
>                 Sing a -> SVect xs -> Dec (VElem a xs)
> isElemSing val SNil = No notInNil
> isElemSing val (SCons x xs) = case decEqSing val x of
>        Yes Refl -> Yes VHere
>        No notHere -> case isElemSing val xs of
>           Yes prf -> Yes (VThere prf)
>           No notThere -> No (notInTail notThere notHere)

ghci:
```
*Part2.Sec9_1> isElemSing s1 (SCons s1 SNil)
Yes
```
