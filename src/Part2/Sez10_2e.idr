
module Part2.Sez10_2e
import Data.List.Views 
import Data.Nat.Views 

%default total

{- some excrcises from sec 10.2 -}

{- equalSuffix excercise, should convert to Haskell (using slower snocList from Sez10_2a_snoc) -}
equalSuffixHelper : Eq a => List a -> List a -> List a
equalSuffixHelper input1 input2 with (snocList input1) 
    equalSuffixHelper [] input2 | Empty = []
    equalSuffixHelper (xs ++ [x]) input2 | (Snoc rec1) with (snocList input2)
        equalSuffixHelper (xs ++ [x]) [] | (Snoc rec1) | Empty = []
        equalSuffixHelper (xs ++ [x]) (ys ++ [y]) | (Snoc rec1) | (Snoc rec2)
              = if x == y then x :: equalSuffixHelper xs ys | rec1 | rec2 else []

equalSuffix : Eq a => List a -> List a -> List a 
equalSuffix xs ys = reverse (equalSuffixHelper xs ys)

{-
idris repl
*Part2/Sez10_2e> equalSuffix [1,2,4,5] [1..5]
[4, 5] : List Integer
-}

{- other excercises use even more advanced views, I expect harder time to create 
performant Haskell version -}

{- toBinary 
uses 

data HalfRec : Nat -> Type where
     HalfRecZ : HalfRec Z
     HalfRecEven : {n : Nat} -> (rec : Lazy (HalfRec n)) -> HalfRec (n + n)
     HalfRecOdd : {n : Nat} -> (rec : Lazy (HalfRec n)) -> HalfRec (S (n + n))
-}
-- TODO the following compiles and prints out gibberish  when executed 
-- toBinary' : Nat -> String
-- toBinary' n with (halfRec n)
--   toBinary' Z | HalfRecZ = "0"
--   toBinary' (x + x) |  HalfRecEven rec = (toBinary' x | rec) ++ "0"
--   toBinary' (S (x + x)) | HalfRecOdd rec = if x == Z then "1" else (toBinary' x | rec) ++ "1"

toBinary : (n : Nat) -> String
toBinary Z = "0"
toBinary k = go k []
  where
    go : (n : Nat) -> (acc : List Char) -> String
    go n acc with (halfRec n)
      go Z acc | HalfRecZ = pack acc
      go (x + x) acc | (HalfRecEven rec) = go x ('0' :: acc) | rec
      go (S (x + x)) acc | (HalfRecOdd rec) = go x ('1' :: acc) | rec

{-
*Part2/Sez10_2e> toBinary 42
"101010" : String
-}

{- palindrome, I expect linear cost vList will be hard to implement -}
palindrome : Eq a => List a -> Bool 
palindrome xs with (vList xs)
   palindrome [] | VNil = True
   palindrome [x] | VOne = True
   palindrome (x :: xs ++ [y]) | VCons rec 
       = if x == y then palindrome xs | rec else False 

{-
idris repl
*Part2/Sez10_2e> :l Part2/Sez10_2e
Type checking ./Part2/Sez10_2e.idr
*Part2/Sez10_2e> palindrome (unpack "abccba")
True : Bool
*Part2/Sez10_2e> palindrome (unpack "abcba")
True : Bool
*Part2/Sez10_2e> palindrome (unpack "abccb")
False : Bool
-}
