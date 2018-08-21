module Part2.Sec5_3_3_dpair
import Data.Vect

{-
Note, Idris figures out Vect size.  
In Haskell "_" == "I do not care"  
In Idris "_" == "You figure it out"
-}
||| Conversion between a list and dependent pair
||| Think about using strong dependent types in runtime calculations.
listToVect : List a -> (n ** Vect n a)
listToVect [] = (_ ** [])
listToVect (x :: xs) = 
        let (_ ** vxs) = listToVect xs
        in (_ ** x :: vxs)
