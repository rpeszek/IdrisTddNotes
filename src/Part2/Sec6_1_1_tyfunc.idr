module Part2.Sec6_1_1_tyfunc
import Data.Vect

{-
Fewer concept == smaller conceptual complexity
type aliasing is simply a type level function!!!
-}

||| Type level function with no params
Position : Type
Position = (Double, Double)

testData : List (Double, Double)
testData = [(1,2),(1,3.1)]

testData' : List Position
testData' = [(1,2),(1,3.1)]

||| Naive test function
sumFirst : List Position -> Double
sumFirst list = sum (map fst list)


||| Type level function with one param
Polygon : Nat -> Type
Polygon n = Vect n Position

tri : Polygon 3
tri = [(0.0, 0.0), (3.0, 0.0), (0.0, 4.0)]

||| One param function acting as type synomym
MyList : Type -> Type
MyList = List

testMyList : MyList Integer -> MyList Integer
testMyList = map (+1) 
