{-
Couple of interesting cases where Idris code generation just shines
-}
module Part2.Sec4_2_2
import Data.Vect

{-
2 case splits and Idris solution search works!
-}
zipV : Vect n a -> Vect n b -> Vect n (a,b)
zipV [] [] = []
zipV (x :: xs) (y :: ys) = (x, y) :: zipV xs ys

{-
Bonus case follows the rules above
-}
zipWithV : (a -> b -> c) -> Vect n a -> Vect n b -> Vect n c 
zipWithV f [] [] = []
zipWithV f (x :: xs) (y :: ys) = f x y :: zipWithV f xs ys

{-
  This is again simple case split on the first variable and Idris finds solutions
-}
appendV : Vect n a -> Vect m a -> Vect (n + m) a  
appendV [] ys = ys
appendV (x :: xs) ys = x :: appendV xs ys
