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
{-# OPTIONS_GHC -fwarn-unused-imports #-}

module Part2.Sez10_2aVect2 where
import Data.Type.Equality
import Data.SingBased.Nat (Nat(..), SNat, type Sing(..), type (+))
import Data.SingBased.NatTheorems
import Data.SingBased.Vect
-- import Data.Singletons

{-
-- Making the IMPOSSIBLE
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

{- | Still constly conversion with extra computational cost of proofs -}
snocVectHelp ::  SNat n -> SNat m -> SnocVect n a -> Vect m a -> SnocVect (n + m) a
snocVectHelp n m snoc VNil = case plusZeroRightNeutral n of Refl -> snoc
snocVectHelp n (SS m) snoc (x ::: xs) 
      = case plusSuccRightSucc n m of Refl -> snocVectHelp (SS n) m (SnocV snoc x) xs

{- | prove Nat laws as I go approach does not improve the cost -}
snocVectHelp' ::  SNat n -> SNat ('S m) -> ('Z + n :~: n + 'Z) -> (n + 'S m) :~: 'S (n + m) -> SnocVect n a -> Vect ('S m) a -> SnocVect (n + ('S m)) a
-- snocVectHelp' n m prf _ snoc VNil = case prf of Refl -> snoc
snocVectHelp' n (SS SZ) _ _ snoc (x ::: VNil) 
      = case plusZeroRightNeutral n of Refl -> case plusSuccRightSucc n (SZ) of Refl -> SnocV snoc x
snocVectHelp' n (SS SZ) px prf snoc xs = undefined -- impossible
snocVectHelp' n (SS (SS m)) prf1 prf2 snoc (x ::: xs) 
      = case prf2 of Refl -> snocVectHelp' (SS n) (SS m) (cong prf1) (adjustProof n m prf2) (SnocV snoc x) xs

-- this still needs induction!
adjustProof :: SNat n -> SNat m -> (n + 'S ('S m)) :~: 'S (n + ('S m))  -> (('S n) + 'S m) :~: 'S (('S n) + m)
adjustProof n m prf = undefined -- case prf of Refl -> Refl



{-| the impossible -}
myReverseHelper :: SnocVect n a -> Vect n a
myReverseHelper EmptyV = VNil
myReverseHelper (SnocV xs x) = x ::: myReverseHelper xs 

{- snocVect is used only once, this is better!-}
myReverse :: Vect n a -> Vect n a
myReverse xs = myReverseHelper $ snocVect xs 

{- 
listWithVect [1..9] (vectToList . myReverse)
-}
