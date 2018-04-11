module Sec8_2
import Data.Vect

%default total 

{- 
 proof is needed for typechecker to replace (k + 1) with (S k) - which is by definition (1 + k) 
 plusCommutative 1 k states that 1 + k = k + 1 or (S k) = k + 1
 `rewrite LHS=RHS in ax` matches on RHS to ax and rewrites ax to LHS type
-}
reverseLemma : Vect (k + 1) elem -> Vect (S k) elem
reverseLemma {k} result = rewrite plusCommutative 1 k in result

myReverse : Vect n elem -> Vect n elem
myReverse [] = []
myReverse (x :: xs) = reverseLemma (myReverse xs ++ [x])

{- 
excercise 1:
Write plusCommutative in terms of
plusZeroRightNeutral : (left : Nat) -> left + 0 = left
plusSuccRightSucc : (left : Nat) -> (right : Nat) -> S (left + right) = left + S right 

Using  
myPlusCommutes (S k) m = plusSuccRightSucc m k
results in error :

...
Specifically:
        Type mismatch between
                plus m (S k)
        and
                plus m (S k)
-}

myPlusCommutes : (n : Nat) -> (m : Nat) -> n + m = m + n
myPlusCommutes Z m = sym (plusZeroRightNeutral m)
-- myPlusCommutes (S k) m = plusSuccRightSucc m k
myPlusCommutes (S k) m = rewrite myPlusCommutes k m in plusSuccRightSucc m k

{- 
Finish the following replacing
reverse' acc [] = ?reverseLemma_nil acc
  reverseLemma_nil : Vect n1 a -> Vect (plus n1 0) a
reverse' acc (x :: xs) = ?reverseLemma_xs (reverse' (x::acc) xs)
  reverseLemma_xs : Vect (S (plus n1 len)) a -> Vect (plus n1 (S len)) a
-}

reverseLemma_nil : Vect n1 a -> Vect (plus n1 0) a
reverseLemma_nil {n1} xs = rewrite plusZeroRightNeutral n1 in xs

reverseLemma_xs :  Vect ((S n1) + len) a -> Vect (plus n1 (S len)) a
reverseLemma_xs {n1} {len} xs = rewrite sym (plusSuccRightSucc n1 len) in xs

-- note, (S n1) + len is defnitionally the same as S (n1 + len)
reverseLemma_test :  Vect ((S n1) + len) a -> Vect (S (n1 + len)) a
reverseLemma_test = id

myReverse2 : Vect n a -> Vect n a
myReverse2 xs = reverse' [] xs
   where reverse' : Vect n a -> Vect m a -> Vect (n+m) a
         reverse' acc [] = reverseLemma_nil acc
         reverse' acc (x :: xs)
                       = reverseLemma_xs (reverse' (x::acc) xs)
