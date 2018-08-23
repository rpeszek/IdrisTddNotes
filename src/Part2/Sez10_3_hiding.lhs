|Markdown version of this file: https://github.com/rpeszek/IdrisTddNotes/wiki/Part2_Sez10_3_hiding
|Idris Src: Sez10_3_hiding.idr

Sections 10.3 View APIs. ShapeView example vs Haskell
=====================================================
Type dependent views can be used to provide pattern matching for client code 
without exposing module implementation details.

Idris code example
------------------  
|IdrisRef: Sez10_3_hiding.idr 

Compared to Haskell
-------------------
Haskell equivalent is not as pretty and not as useful. 
I am implementing `area` that works on type level shapes and type level sizes.
I am using manually defined fractional type `Frac` in place of a language 
built-in `Double`.  
This code does not try to achieve equivalent implementation hiding, rather,
it is an experiment in writing a somewhat similar code in Haskell where 
`triangle`, `rectangle`, and `circle` are used on the type level.

> {-# LANGUAGE 
>    TemplateHaskell
>    , GADTs
>    , TypeFamilies
>    , DataKinds
>    , KindSignatures
>    , UndecidableInstances
>    , TypeInType
>    , ScopedTypeVariables 
> #-}
> {-# OPTIONS_GHC -fwarn-incomplete-patterns #-}
> 
> module Part2.Sez10_3_hiding where
> import Data.Singletons
> import Data.Singletons.TH
> import Data.Kind (Type)
> import Data.Singletons.SuppressUnusedWarnings
> import Data.SingBased
>
> $(singletons [d|
>   data Shape a = MkTriangle a a
>           | MkRectangle a a
>           | MkCircle a
> 
>   triangle :: a -> a -> Shape a
>   triangle = MkTriangle
> 
>   rectangle :: a -> a -> Shape a
>   rectangle = MkRectangle
> 
>   circle :: a -> Shape a
>   circle = MkCircle
>   
>   data Frac = MkFrac Nat Nat deriving Show
>
>   |])
>
> -- | could be placed inside singletons template too
> fmulti :: Frac -> Frac -> Frac 
> fmulti (MkFrac n1 n2) (MkFrac m1 m2) = MkFrac (multi n1 m1) (multi n2 m2)
>   
> showFrac :: Frac -> String 
> showFrac (MkFrac n m) = show (natToInteger n) ++ "/" ++ show (natToInteger m) 
> 
> sF1 = SMkFrac s1 s1 -- `1' as `Sing frac`

ghci:
```
*Part2.Sez10_3_hiding> :t sF1
sF1 :: Sing ('MkFrac ('S 'Z) ('S 'Z))
```

Idris' definition of `ShapeView` translates quite nicely to Haskell.

> data ShapeView (s :: Shape a) where
>     SvTriangle :: Sing sbase -> Sing sheight -> ShapeView (Triangle sbase sheight)
>     SvRectangle :: Sing swidth -> Sing sheight -> ShapeView (Rectangle swidth sheight)
>     SvCircle :: Sing sradius -> ShapeView (Circle sradius)

Interestingly, this ShapeView is isomorphic to singletons generated `SShape` 

> shapeView :: forall (s :: Shape a) . Sing s -> ShapeView s
> shapeView (SMkTriangle a b) = SvTriangle a b
> shapeView (SMkRectangle a b) = SvRectangle a b
> shapeView (SMkCircle a) = SvCircle a

so using the `ShapeView` is redundant to the constructs already defined in `singletons`.
Instead of `SomeSing Frac` I am using the isomorphic `Frac` directly.

> approxPi = MkFrac (integerToNat 22) (integerToNat 7)
> 
> area :: forall (s :: Shape Frac) . Sing s -> Frac
> area s = case shapeView s of
>   SvTriangle sbase sheight -> let fhalf = (MkFrac (integerToNat 1) (integerToNat 2)) 
>                               in fhalf `fmulti` (fromSing sbase) `fmulti` (fromSing sheight) 
>   SvRectangle swidth sheight -> (fromSing swidth) `fmulti` (fromSing sheight)
>   SvCircle sradius -> approxPi `fmulti` (fromSing sradius) `fmulti` (fromSing sradius) 
>
> area' :: forall (s :: Shape Frac) . Sing s -> Frac
> area' s = case s of
>   SMkTriangle sbase sheight -> let fhalf = (MkFrac (integerToNat 1) (integerToNat 2)) 
>                               in fhalf `fmulti` (fromSing sbase) `fmulti` (fromSing sheight) 
>   SMkRectangle swidth sheight -> (fromSing swidth) `fmulti` (fromSing sheight)
>   SMkCircle sradius -> approxPi `fmulti` (fromSing sradius) `fmulti` (fromSing sradius) 

ghci:
```
*Part2.Sez10_3_hiding> showFrac $ area' (sCircle sF1)
"22/7"
*Part2.Sez10_3_hiding> showFrac $ area' (sRectangle sF1 sF1)
"1/1"
```
