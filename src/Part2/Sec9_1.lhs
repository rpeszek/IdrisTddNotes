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

This will not compile
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

and I can mimic Idris's removeElem using type families

> type family RemoveElem (val :: a) (xs :: Vect (S n) a) (prf :: VElem val xs) :: Vect n a where
>   RemoveElem val (val '::: xs) VHere = xs
>   RemoveElem val (y '::: ys) (VThere later) = y '::: RemoveElem val ys later
>
> data Test (a :: Vect ('S 'Z) Symbol) where
>    Test :: Test (RemoveElem "str" ("hello" '::: "str" '::: 'Nil) strInVect)  

Use of TypeFamiles has limitations but this example came close!


`isElem` example
----------------

For this example, I am switching to use of `singletons.  
The `isElem` example uses empty match instead of `impossible` keyword

> data SVElem (ax :: a) (vx :: SingV.Vect k a) where
>         SVHere :: SVElem x (x 'SingV.::: xs)
>         SVThere :: SVElem x xs -> SVElem x (y 'SingV.::: xs)
> deriving instance Show (SVElem a b)
>
> notInNil :: SVElem ax 'SingV.Nil -> Void
> notInNil x = case x of { }
>
> notInTail ::  (SVElem ax xs -> Void) ->
>                    ((Sing ax :~: Sing x) -> Void) -> SVElem ax (x 'SingV.::: xs) -> Void
> notInTail notThere notHere SVHere = notHere Refl
> notInTail notThere notHere (SVThere later) = notThere later

Note, even using `TypeInType`, I was not able to auto-generate singletons for `Vect n a` itself.
But I implemented it by hand.  
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
But narrowing the scope to just `Nat` vectors works

> isElemNat :: SingV.SNat n -> SingV.SVect xs -> Dec (SVElem n xs)
> isElemNat val SingV.SNil = No notInNil
> isElemNat val (SingV.SCons x xs) = case decEq val x of
>        Yes Refl -> Yes SVHere
>        No notHere -> case isElemNat val xs of
>           Yes prf -> Yes (SVThere prf)
>           No notThere -> No (notInTail notThere notHere)

and is the same way as Idris.
