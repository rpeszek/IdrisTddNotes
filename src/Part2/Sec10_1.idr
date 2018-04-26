
module Part2.Sec10_1 

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

|||slow reverse
covering
myReverse : List a -> List a
myReverse input with (listLast input)
    myReverse [] | Empty = []
    myReverse (xs ++ [x]) | (NonEmpty xs x) = x :: myReverse xs


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
     each step removes 2 elements from the counter and adds new elements to the left 
     when counter is excausted all elements are added to the right -}
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


-- TODO 
-- excercises
