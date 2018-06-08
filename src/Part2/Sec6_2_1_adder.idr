module Part2.Sec6_2_1_adder

{- 
Think of this type as type level function 
second case maps AdderType to a function type
-}
AdderType : (numargs : Nat) -> Type
AdderType Z = Int
AdderType (S k) = (nextArg : Int) -> AdderType k

||| adder numargs acc nums...
||| adder 0 : Int -> Int
||| adder 1 : Int -> Int -> Int
||| adder 2 : Int -> Int -> Int -> Int
||| adder 2 : Int -> Int -> Int -> Int
adder : (numargs : Nat) -> (acc : Int) -> AdderType numargs
adder Z acc = acc
adder (S k) acc = \nextArg => adder k (nextArg + acc)
