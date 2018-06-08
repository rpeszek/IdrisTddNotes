
module Part2.Sez10_2b
import Part2.Sez10_2a_snoc

%default total 

isSuffix : Eq a => List a -> List a -> Bool
isSuffix input1 input2 with (snocList input1)
    isSuffix [] input2 | Empty = True
    isSuffix (xs ++ [x]) input2 | (Snoc rec1) with (snocList input2)
        isSuffix (xs ++ [x]) [] | (Snoc rec1) | Empty = False
        isSuffix (xs ++ [x]) (ys ++ [y]) | (Snoc rec1) | (Snoc rec2)
              = if x == y then isSuffix xs ys | rec1 | rec2 else False

{-
idris repl:
*Part2/Sez10_2b> isSuffix [7,8,9,10] [1..10]
True : Bool
*Part2/Sez10_2b> isSuffix [7,8,9] [1..10]
False : Bool
-}
