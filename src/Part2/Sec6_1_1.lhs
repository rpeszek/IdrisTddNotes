|Markdown version of this file: https://github.com/rpeszek/IdrisTddNotes/wiki/idrVsHs_Part2_Sec6_1_1
|Idris Src: Sec6_1_1.idr

Section 6.1.1. Type level functions as type synonyms vs Haskell
===============================================================

Idris code example
------------------  
|IdrisRef: Sec6_1_1.idr 

idris repl
```
*src/Part2/Sec6_1_1> sumFirst testData
2.0 : Double
*src/Part2/Sec6_1_1> sumFirst testData'
2.0 : Double

*src/Part2/Sec6_1_1> tri
[(0.0, 0.0), (3.0, 0.0), (0.0, 4.0)] : Vect 3
                                            (Double, Double)
*src/Part2/Sec6_1_1> :t tri
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
> module Part2.Sec6_1_1 where
> import Part2.Sec3_2_3 (Vect(..))
> import Part2.Sec5_3_3 (VectUnknown, SNat, listToVect)
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

Idris shines!
