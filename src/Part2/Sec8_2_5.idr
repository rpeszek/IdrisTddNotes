{- vector append in reverse order -}
module Sec8_2_5
import Data.Vect

%default total 

myAppend1 : Vect n a -> Vect m a -> Vect (n + m) a
myAppend1 [] ys = ys
myAppend1 (x :: xs) ys = x :: myAppend1 xs ys

{- reverse order -}
myAppend2_xs_lemma : Vect (S (m + k)) elem -> Vect (plus m (S k)) elem
myAppend2_xs_lemma {m} {k} xs = rewrite sym
                       (plusSuccRightSucc m k) in xs

myAppend2 : Vect n elem -> Vect m elem -> Vect (m + n) elem
myAppend2 {m} [] ys = rewrite plusZeroRightNeutral m in ys
myAppend2 (x :: xs) ys = myAppend2_xs_lemma (x :: myAppend2 xs ys)
