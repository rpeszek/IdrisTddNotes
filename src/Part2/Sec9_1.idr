{-
Code examples about 

data Elem : a -> Vect k a -> Type where
     Here : Elem x (x :: xs)
     There : (later : Elem x xs) -> Elem x (y :: xs)

and

isElem : DecEq a => (value : a) -> (xs : Vect n a) -> Dec (Elem value xs)
-}

module Part2.Sec9_1
import Data.Vect

%default total 

{- This type of code derives automatically with term search !-}
twoTest : Elem 2 [1,2,3]
twoTest = There Here

{- 
second condition derived via interactive development resulted in absurd and I just 
commented it out, the function is still total, uncommented compiles too

Note:
absurd : Uninhabited t => t -> a
later is uninhabited 
-}
removeElem : (value : a) -> (xs : Vect (S n) a) ->
                   (prf : Elem value xs) ->
                   Vect n a
removeElem value (value :: ys) Here = ys
-- removeElem {n = Z} value (y :: []) (There later) = absurd later
removeElem {n = (S k)} value (y :: ys) (There later) = y :: removeElem value ys later

removeElem_auto : (value : a) -> (xs : Vect (S n) a) ->
                  {auto prf : Elem value xs} -> Vect n a
removeElem_auto value xs {prf} = removeElem value xs prf


{-
repl:
*Part2/Sec9_1> removeElem 2 [1,2,3,4,5] (There Here)
[1, 3, 4, 5] : Vect 4 Integer

*Part2/Sec9_1> removeElem_auto 2 [1,2,3,4,5]
[1, 3, 4, 5] : Vect 4 Integer
-}

data Test : (Vect 1 String) -> Type where
   MkTest : Test (removeElem_auto "str" ["hello", "str"]) 

data Test1 : (Vect 1 String) -> Type where
   MkTest1 : Test1 (removeElem "str" ["hello", "str"] (There Here)) 

{-
Note: removeElem is resolved at compile time, same it true for Haskell
repl: 
*Part2/Sec9_1> :t MkTest
MkTest : Test (removeElem_auto "str" ["hello", "str"])

*Part2/Sec9_1> :t MkTest1
MkTest1 : Test1 (removeElem "str" ["hello", "str"] (There Here))
-}

{-
However: this does not compile :) but it does in Haskell :(
data TestWrong : (Vect 1 String) -> Type where
   MkTestWrong : TestWrong (removeElem "str1" ["hello", "str"] (There Here))  

Compiler error:
   |
57 |    MkTestWrong : TestWrong (removeElem "str1" ["hello", "str"] (There Here))  
   |                                                                 ~~~~~~~~~~
When checking type of Part2.Sec9_1.MkTestWrong:
When checking argument later to constructor Data.Vect.There:
        Type mismatch between
                Elem x (x :: xs) (Type of Here)
        and
                Elem "str1" ["str"] (Expected type)
        
        Specifically:
                Type mismatch between
                        "str1"
                and
                        "str"
-}

{- 
 Type safe version of elem function 
 elem : Eq ty => (value : ty) -> (xs : Vect n ty) -> Bool
 -}
notInNil : Elem value [] -> Void
notInNil Here impossible
notInNil (There _) impossible

notInTail : (notThere : Elem value xs -> Void) ->
                    (notHere : (value = x) -> Void) -> Elem value (x :: xs) -> Void
notInTail notThere notHere Here = notHere Refl
notInTail notThere notHere (There later) = notThere later

isElem' : DecEq a => (value : a) -> (xs : Vect n a) -> Dec (Elem value xs)
isElem' value [] = No notInNil
isElem' value (x :: xs) = case decEq value x of
          Yes Refl => Yes Here
          No notHere => case isElem' value xs of
                             Yes prf => Yes (There prf)
                             No notThere => No (notInTail notThere notHere)

{-
*Part2/Sec9_1> isElem 1 [2,3,1]
Yes (There (There Here)) : Dec (Elem 1 [2, 3, 1])
-}
