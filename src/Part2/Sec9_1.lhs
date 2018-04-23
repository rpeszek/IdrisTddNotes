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
> import Util.NonLitsNatAndVector
> import qualified Util.SingVector as SingV
> import Util.SingVector (type FromTL)
> import GHC.TypeLits
> import Data.Kind (Type)
> import Data.Void
> import Data.Type.Equality
> import Data.Singletons
> import Part2.Sec8_3 
> 
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

The same approach works for Vectors

> data VElem (ax :: a) (vx :: Vect k a) where
>         VHere :: VElem x (x '::: xs)
>         VThere :: VElem x xs -> VElem x (y '::: xs)
> deriving instance Show (VElem a b)
>
> twoInVect :: VElem 2 (1 '::: 2 '::: 3 '::: 'Nil)
> twoInVect = VThere VHere
>
> strInVect :: VElem "str" ("hello" '::: "str" '::: 'Nil)
> strInVect = VThere VHere

and it works for my `singletons` implementation of Vector

> data SVElem (ax :: a) (vx :: SingV.Vect k a) where
>         SVHere :: SVElem x (x 'SingV.::: xs)
>         SVThere :: SVElem x xs -> SVElem x (y 'SingV.::: xs)
> deriving instance Show (SVElem a b)

`Uninhabited`
-------------
`Data.Void` defines function `absurd :: Void -> a` which mimics `void` in Idris.

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

> removeElem :: forall (n :: SingV.Nat) (val :: a) (xs :: SingV.Vect (SingV.S n) a) . SingKind a =>
>       SingV.SNat n -> Sing val ->  SingV.SVect xs -> SVElem val xs -> SingV.Vect n (Demote a)
> removeElem _ val (_ `SingV.SCons` ys) SVHere = SingV.sVectToVect ys
> removeElem (SingV.SS n1) val (y `SingV.SCons` ys) (SVThere later) = (fromSing y) SingV.::: (removeElem n1 val ys later)
> {- While Idris knows that the following case is invalid, 
>  GHC picks is up as error: Pattern match(es) are non-exhaustive
>  attempt to implement it as `absurd' later` causes compilation errors
> -}
> removeElem SingV.SZ val (SingV.SCons _ SingV.SNil) (SVThere later) = undefined -- absurd' later
>
> testRemoveElem = removeElem SingV.s0 SingV.s3 (SingV.SCons SingV.s3 SingV.SNil) SVHere

ghci:
```
*Part2.Sec9_1> testRemoveElem
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
*Part2.Sec9_1> :kind! (RemoveElem "str" ("hello" '::: "str" '::: 'Nil) ('VThere 'VHere))
(RemoveElem "str" ("hello" '::: "str" '::: 'Nil) ('VThere 'VHere)) :: Vect
                                                                        ('S 'Z) Symbol
= "hello" '::: 'Nil

*Part2.Sec9_1> :kind! (RemoveElem "str1" ("hello" '::: "str" '::: 'Nil) ('VThere 'VHere))

<interactive>:1:52: error:
    • Expected kind ‘VElem "str1" ("hello" '::: ("str" '::: 'Nil))’,
        but ‘'VThere 'VHere’ has kind ‘VElem
                                         "str1" ("hello" '::: ("str1" '::: 'Nil))’
    • In the third argument of ‘RemoveElem’, namely
        ‘( 'VThere  'VHere)’
      In the type ‘(RemoveElem "str1" ("hello"
                                     ::: ("str" :::  'Nil)) ( 'VThere  'VHere))’
```
Good! 
 
The following code is not very useful (similarly to Idris `RemoveElem` is not resolved)

> data Test (a :: Vect ('S 'Z) Symbol) where
>    Test :: Test (RemoveElem "str" ("hello" '::: "str" '::: 'Nil) strInVect) 

`Test` compiles (because size is reduced by type family, but there is no evidence of type family actually working.

Unlike Idris, the following also compiles :( 

> data TestWrong (a :: Vect ('S 'Z) Symbol) where
>    TestWrong :: TestWrong (RemoveElem "str1" ("hello" '::: "str" '::: 'Nil) strInVect)  

TODO I need to study these limitations more.

Interestingly `RemoveElem` also complies when I include the absurd case! 

> type family RemoveElem' (val :: a) (xs :: Vect (S n) a) (prf :: VElem val xs) :: Vect n a where
>   RemoveElem' val (val '::: xs) 'VHere = xs
>   RemoveElem' val (y '::: 'Nil) ('VThere later) = VoidF (UninhabitedF later)
>   RemoveElem' val (y '::: ys) ('VThere later) = y '::: RemoveElem' val ys later
>

I can type the not logical case to invoke the uninhabited case for `RemoveElem'`
and the corresponding case is just not reduced for `RemoveElem`  
ghci:
```
*Part2.Sec9_1> :kind! (RemoveElem' "na" ("str" '::: 'Nil) ('VThere _))
(RemoveElem' "na" ("str" '::: 'Nil) ('VThere _)) :: Vect 'Z Symbol
= VoidF (UninhabitedF _)

*Part2.Sec9_1> :kind! (RemoveElem "na" ("str" '::: 'Nil) ('VThere _))
(RemoveElem "na" ("str" '::: 'Nil) ('VThere _)) :: Vect 'Z Symbol
= RemoveElem "na" ("str" '::: 'Nil) ('VThere _)
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

For this example, I am again switching to using `singletons`.  
The `isElem` example uses `EmptyCase` instead of the `impossible` Idris keyword

> notInNil :: SVElem ax 'SingV.Nil -> Void
> notInNil x = case x of { }
>
> notInTail ::  (SVElem ax xs -> Void) ->
>                    ((Sing ax :~: Sing x) -> Void) -> SVElem ax (x 'SingV.::: xs) -> Void
> notInTail notThere notHere SVHere = notHere Refl
> notInTail notThere notHere (SVThere later) = notThere later

The following, unfortunately, does not seem to work (TODO)

> isElem :: DecEq (Sing :: a -> Type) => Sing a -> SingV.SVect xs -> Dec (SVElem a xs)
> isElem val SingV.SNil = No notInNil
> isElem val (SingV.SCons x xs) = undefined

use of `case decEq val x` or even `case decEq val val` on the RHS of the second case split
```
isElem val (SingV.SCons x xs) = case decEq val val of
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

> isElemNat :: SingV.SNat n -> SingV.SVect xs -> Dec (SVElem n xs)
> isElemNat val SingV.SNil = No notInNil
> isElemNat val (SingV.SCons x xs) = case decEq val x of
>        Yes Refl -> Yes SVHere
>        No notHere -> case isElemNat val xs of
>           Yes prf -> Yes (SVThere prf)
>           No notThere -> No (notInTail notThere notHere)

and the code is the same as in Idris.
