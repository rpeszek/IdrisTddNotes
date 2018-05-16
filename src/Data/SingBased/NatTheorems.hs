{-# LANGUAGE 
    TypeOperators
  , DataKinds
  , GADTs
  , TypeFamilies
  , KindSignatures
  , PolyKinds
#-}
{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}

{- This module reimplements Nat theorems from Part2.Sec8_2_5 for Data.SingBased.Nat -}
module Data.SingBased.NatTheorems where

import Data.SingBased.Nat
import Data.Type.Equality ((:~:)(Refl), sym)

{- type level function -}
type family F (a :: k1) :: k2 
type instance F n = 'S n

-- type family is a type level partial function so if x = y => f x = f y
cong :: (x :~: y) -> F x :~: F y
cong Refl = Refl 

{- 
  cong makes it more explit but it is not needed.
  I could use 
   case plusSuccRightSucc left right of Refl -> Refl instead.
 -}
plusZeroRightNeutral :: SNat mx -> 'Z + mx :~: mx + 'Z
plusZeroRightNeutral SZ     = Refl
plusZeroRightNeutral (SS k) = cong (plusZeroRightNeutral k)

plusSuccRightSucc :: SNat left -> SNat right -> (left + 'S right) :~: 'S (left + right)
plusSuccRightSucc SZ right        = Refl
plusSuccRightSucc (SS left) right = cong $ plusSuccRightSucc left right 

plusCommutative :: SNat left -> SNat right -> ((left + right) :~: (right + left))
plusCommutative SZ right = plusZeroRightNeutral right
plusCommutative (SS k) right = case plusCommutative k right of Refl -> sym (plusSuccRightSucc right k)
