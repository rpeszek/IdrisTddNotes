{- 
 SnocList and liner cost reverse examples from 10.2.1 and 10.2.2 
 "snoc" == reverse "cons"
-}

module Part2.Sez10_2a_snoc

%default total 

public export
data SnocList : List a -> Type where
     Empty : SnocList []
     Snoc : (rec : SnocList xs) -> SnocList (xs ++ [x])

export
snocList : (xs : List a) -> SnocList xs

snocListHelp : (snoc : SnocList input) -> (rest : List a) ->
               SnocList (input ++ rest)
snocListHelp {input} snoc [] = rewrite appendNilRightNeutral input in snoc
snocListHelp {input} snoc (x :: xs) = rewrite appendAssociative input [x] xs in
                     snocListHelp (Snoc snoc {x}) xs

snocList xs = snocListHelp Empty xs

||| reverse based on SnocList view, implementation that avoids using Helper function
export
myReverse : List a -> List a
-- with argument is not recreated in recursive step
myReverse input with (snocList input)
  myReverse [] | Empty = []
  myReverse (xs ++ [x]) | (Snoc rec) = x :: myReverse xs | rec -- passed with argument

{-
idris repl:
*Part2/Sec10_2a> myReverse [1..10]
[10, 9, 8, 7, 6, 5, 4, 3, 2, 1] : List Integer
*Part2/Sec10_2a> :t appendNilRightNeutral
appendNilRightNeutral : (l : List a) -> l ++ [] = l
*Part2/Sec10_2a> :t appendAssociative
appendAssociative : (l : List a) ->
                    (c : List a) -> (r : List a) -> l ++ c ++ r = (l ++ c) ++ r
-}
