|Markdown version of this file: https://github.com/rpeszek/IdrisTddNotes/wiki/Part2_Sec6_1_1_tyfunc
|Idris Src: Sec6_1_1_tyfunc.idr

Section 6.1.1. Type level functions as type synonyms vs Haskell
===============================================================

Idris code example
------------------  
|IdrisRef: Sec6_1_1_tyfunc.idr 

idris repl
```
*src/Part2/Sec6_1_1_tyfunc> sumFirst testData
2.0 : Double
*src/Part2/Sec6_1_1_tyfunc> sumFirst testData'
2.0 : Double

*src/Part2/Sec6_1_1_tyfunc> tri
[(0.0, 0.0), (3.0, 0.0), (0.0, 4.0)] : Vect 3
                                            (Double, Double)
*src/Part2/Sec6_1_1_tyfunc> :t tri
tri : Polygon 3
```
Compared to Haskell
-------------------
Idris simplifies things by removing concept of `type` synonyms.
Haskell can use type families instead of type synonyms as well.
Idris seems much simpler.
 
> {-# LANGUAGE  
>    TypeFamilies
>  , DataKinds
> #-}
> {-# OPTIONS_GHC -fwarn-unused-imports #-}
>
> module Part2.Sec6_1_1_tyfunc where
> import Part2.Sec3_2_3_gen (Vect(..))
> import Part2.Sec5_3_3_dpair (VectUnknown, listToVect)
> import Data.Kind (Type)
> import GHC.TypeLits
>
> {- Using type synomyms -}
> type Position = (Double, Double)
> type Polygon n = Vect n Position
>
> {-| Naive test function -}
> sumFirst :: [Position] -> Double
> sumFirst list = sum (map fst list)
>
> tri :: Polygon 3
> tri = (0.0, 0.0) ::: ((3.0, 0.0) ::: ((0.0, 4.0) ::: VNil))
> 
> type PolygonUnk = VectUnknown Position
> 
> triUnk :: PolygonUnk
> triUnk = listToVect [(0.0, 0.0), (3.0, 0.0), (0.0, 4.0)]
>
> {- Using Type families -}
> type family Position' :: Type where
>    Position' = (Double, Double) 
>
> type family Polygon' (n :: Nat) :: Type where
>     Polygon' n = Vect n (Double, Double) 
>
> {-| Naive test function using list of Type families!-}
> sumFirst' :: [Position'] -> Double
> sumFirst' list = sum (map fst list)
>
> tri' :: Polygon' 3
> tri' = (0.0, 0.0) ::: ((3.0, 0.0) ::: ((0.0, 4.0) ::: VNil))

The other big improvement is that in Idris type level functions are, well functions.
In Haskell, type families have limitations, for example type family cannot be partially applied
when used as a type variable.  That is why `singletons` uses all these strange `Sym0`, `Sym1` types. 

