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
>   -- , ScopedTypeVariables
>   , StandaloneDeriving
>   , KindSignatures
>   , TypeInType
>   , AllowAmbiguousTypes
> #-}
> {-# OPTIONS_GHC -fwarn-incomplete-patterns #-}
>
> module Part2.Sec9_1 where
> import Util.NonLitsNatAndVector
> import GHC.TypeLits
> import Data.Kind (Type)
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

Same approach works for Vectors

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
