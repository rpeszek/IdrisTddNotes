{-# LANGUAGE 
   TypeOperators
   , GADTs
   , TypeFamilies
   , DataKinds
   , PolyKinds
   , ScopedTypeVariables 
   , TypeInType
#-}
{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}

module Part2.Sez10_2aVect2 where
import Data.Type.Equality
import Data.SingBased.Nat (Nat(..), SNat, type Sing(..), type (+))
import Data.SingBased.NatTheorems
import Data.SingBased.Vect
import Data.Singletons

{-
-- IMPOSSIBLE!
myReverseL3 :: [a] -> [a]
myReverseL3 [] = []
myReverseL3 (xs ++ [x]) = x : myReverseL3 xs

(this is really exactly the same as reverse2)
 -}

data SnocVect n a where
     EmptyV :: SnocVect 'Z a
     SnocV :: SnocVect n a -> a -> SnocVect ('S n) a

snocVect :: Vect n a -> SnocVect n a
snocVect xs = snocVectHelp SZ (vlength xs) EmptyV xs

snocVectHelp ::  SNat n -> SNat m -> SnocVect n a -> Vect m a -> SnocVect (n + m) a
snocVectHelp n m snoc VNil = case plusZeroRightNeutral n of Refl -> snoc
snocVectHelp n (SS m) snoc (x ::: xs) 
      = case plusSuccRightSucc n m of Refl -> snocVectHelp (SS n) m (SnocV snoc x) xs

{-| the impossible -}
myReverseHelper :: SnocVect n a -> Vect n a
myReverseHelper EmptyV = VNil
myReverseHelper (SnocV xs x) = x ::: myReverseHelper xs 

{- snocVect is used only once, this has linear cost!-}
myReverse :: Vect n a -> Vect n a
myReverse xs = myReverseHelper $ snocVect xs 

{- 
listWithVect [1..9] (vectToList . myReverse)
-}
