{- Sez10_1 instead of Sec10_1 to recover alphabetical sort -}
module Part2.Sez10_1 

%default total 

{- ListLast view examples -}
data ListLast : List a -> Type where 
   Empty : ListLast [] 
   NonEmpty : (xs : List a) -> (x : a) -> ListLast (xs ++ [x])

total
listLast : (xs : List a) -> ListLast xs
listLast [] = Empty
listLast (x :: xs) = case listLast xs of
      Empty => NonEmpty [] x
      NonEmpty ys y => NonEmpty (x :: ys) y


describeHelper : (input : List Int) -> ListLast input -> String
describeHelper [] Empty = "Empty"
describeHelper (xs ++ [x]) (NonEmpty xs x)
        = "Non-empty, initial portion = " ++ show xs

describeListEnd : List Int -> String
describeListEnd xs = describeHelper xs (listLast xs)

{- cool with syntax adds additional arguments to function implementation -}
describeListEnd' : List Int -> String
describeListEnd' input with (listLast input)
  describeListEnd' [] | Empty = "Empty"
  describeListEnd' (xs ++ [x]) | (NonEmpty xs x)
          = "Non-empty, initial portion = " ++ show xs

|||slow reverse - ListLast view is rebuilt in each recursive step
covering
myReverse : List a -> List a
myReverse input with (listLast input)
    myReverse [] | Empty = []
    myReverse (xs ++ [x]) | (NonEmpty xs x) = x :: myReverse xs

{- 
idris repl:
*Part2/Sez10_1> myReverse [5,2,7,1]
[1, 7, 2, 5] : List Integer
-}

{- SplitList, merge sort example -}
data SplitList : List a -> Type where
     SplitNil : SplitList []
     SplitOne : SplitList [x]
     SplitPair : (lefts : List a) -> (rights : List a) ->
                 SplitList (lefts ++ rights)

total
splitList : (input : List a) -> SplitList input
splitList input = splitListHelp input input
where
  {- the first list acts as a counter only, 
     each step removes 2 elements from the counter and adds new elements to `lefts` 
     when counter is excausted all elements are added to `rights` -}
  splitListHelp : List a -> (input : List a) -> SplitList input
  splitListHelp _ [] = SplitNil
  splitListHelp _ [x] = SplitOne
  splitListHelp (_ :: _ :: counter) (item :: items)
       = case splitListHelp counter items of
              SplitNil => SplitOne  --cool how Idris figures this out!
              SplitOne {x} => SplitPair [item] [x]
              SplitPair lefts rights => SplitPair (item :: lefts) rights
  splitListHelp _ items = SplitPair [] items

covering
mergeSort : Ord a => List a -> List a
mergeSort input with (splitList input)
   mergeSort [] | SplitNil = []
   mergeSort [x] | SplitOne = [x]
   mergeSort (lefts ++ rights) | (SplitPair lefts rights)
                 -- merge : Ord a => List a -> List a -> List a
                 = merge (mergeSort lefts) (mergeSort rights)

{-
idris repl: 
*Part2/Sez10_1> mergeSort [5,2,7,1]
[1, 2, 5, 7] : List Integer
-}

-- excercises
data TakeN : List a -> Type where
      Fewer : TakeN xs
      Exact : (n_xs : List a) -> TakeN (n_xs ++ rest)
         
takeN : (n : Nat) -> (xs : List a) -> TakeN xs
takeN Z xs = Exact []  --kinda amazing how much Idris infers here!
takeN (S k) [] = Fewer 
takeN (S k) (x :: xs) = case takeN k xs of 
       Fewer => Fewer
       Exact rxs => Exact (x :: rxs)

covering
groupByN : (n : Nat) -> (xs : List a) -> List (List a)
groupByN n xs with (takeN n xs)
  groupByN n xs | Fewer = [xs]
  groupByN n (n_xs ++ rest) | (Exact n_xs) = n_xs :: groupByN n rest

{-
idris repl:
*Part2/Sez10_1> groupByN 3 [1..10]
[[1, 2, 3], [4, 5, 6], [7, 8, 9], [10]] : List (List Integer)
-}

-- excercise 2
-- use of div forces `partial` here
partial
halves : List a -> (List a, List a)
halves list with (takeN ((length list) `div` 2) list)
   halves list | Fewer = (list, [])
   halves (half1 ++ half2) | (Exact half1) = (half1, half2)

{-
*Part2/Sez10_1> halves [1..10]
([1, 2, 3, 4, 5], [6, 7, 8, 9, 10]) : (List Integer, List Integer)
*Part2/Sez10_1> halves [1]
([], [1]) : (List Integer, List Integer)
*Part2/Sez10_1> the (List Integer, List Integer) (halves [])
([], []) : (List Integer, List Integer)
-} 
