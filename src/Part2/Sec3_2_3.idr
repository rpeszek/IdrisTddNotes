module Part2.Sec3_2_3
import Data.Vect

{-
implementation code generated 100% by idris
steps:
 * Add def with cursor on mapV (Ctr-Alt-a)
 * Case split xs (Ctr-Alt-c)
 * Search (Crl-Alt-s) for both holes
-}
mapV : (a -> b) -> Vect n a -> Vect n b
mapV f [] = []
mapV f (x :: xs) = f x :: mapV f xs

mapV2 : (a -> b) -> Vect n a -> Vect n b
mapV2 f [] = ?mapV2_rhs_1
mapV2 f (x :: xs) = ?mapV2_rhs_2
