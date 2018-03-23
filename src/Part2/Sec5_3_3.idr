module Part2.Sec5_3_3
import Data.Vect

{-
Note, Idris figures out Vect size.
-}
||| Conversion between a list and dependent pair
listToVect : List a -> (n ** Vect n a)
listToVect [] = (_ ** [])
listToVect (x :: xs) = 
        let (_ ** vsx) = listToVect xs
        in (_ ** x :: vsx)
