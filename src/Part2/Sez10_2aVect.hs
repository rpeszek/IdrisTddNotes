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

module Part2.Sez10_2aVect where
import Data.Type.Equality
import Data.SingBased.Nat (Nat(..), type SNat, type Sing(..), integerToNat, natToInteger, s1)
import Data.SingBased.Vect
import Data.Singletons
import Data.SingBased.NatTheorems (plusCommutative)

{- To work with SnocVect view I need to prove things like
`(VAppend v 'VNil) :~: v`
which is not doable because of kind mismatch. 
Hence this code uses :~~:.  
`Data.Type.Equality` does not provide  :~~: euquivalent of `sym` 
 -}
hsym :: (a :~~: b) -> (b :~~: a)
hsym HRefl = HRefl

data SnocVect (v :: Vect n a) where
   EmptyV :: SnocVect 'VNil
   SnocV :: forall (xs :: Vect n a) (x :: a). 
                 SnocVect xs -> Sing x -> SnocVect (VAppend xs (VOneElem x))

snocVectHelp :: forall (input :: Vect n a) (rest :: Vect m a) . 
                 Sing input -> SnocVect input -> Sing rest -> SnocVect (VAppend input rest)
snocVectHelp input snoc SVNil = case hsym (vappendVNilRightNeutral input) of HRefl -> snoc
snocVectHelp input snoc (SVCons x xs) 
      = case hsym (vappendAssociative input (sVOneElem x) xs) of
           HRefl -> snocVectHelp (sVAppend input (sVOneElem x)) (SnocV snoc x) xs 



{-| See comment below for problems with replacing `Sing vect` with `SNat n`-}
vappendVNilRightNeutral :: forall (v :: Vect n a) . Sing v -> (VAppend v 'VNil) :~~: v
vappendVNilRightNeutral SVNil = HRefl
vappendVNilRightNeutral (SVCons x xs) = case vappendVNilRightNeutral xs of HRefl -> HRefl


vappendAssociative ::  forall (l :: Vect n a) (c :: Vect m a) (r :: Vect k a) .
      Sing l -> Sing c -> Sing r -> VAppend l (VAppend c r) :~~: VAppend (VAppend l c) r
vappendAssociative SVNil c r = HRefl
vappendAssociative (SVCons x xs) c r = case vappendAssociative xs c r of HRefl -> HRefl


snocVect :: forall (xs :: Vect n a). Sing xs -> SnocVect xs
snocVect xs = snocVectHelp SVNil EmptyV xs

myReverseHelper :: forall (v :: Vect n a) . SnocVect v -> SomeKnownSizeVect n a
myReverseHelper EmptyV = MkSomeKnownSizeVect SZ SVNil 
myReverseHelper (SnocV sxs x) = case myReverseHelper sxs of
         MkSomeKnownSizeVect k sv -> case plusCommutative k s1 of Refl -> MkSomeKnownSizeVect (SS k) (SVCons x sv)

myReverse :: (SingKind k) => Vect n (Demote k) -> Vect n (Demote k)
myReverse v = case vectToSomeKnownSizeVect v of 
                   MkSomeKnownSizeVect n xs -> someKnownSizeVectToVect . myReverseHelper . snocVect $ xs 

testMyReverseWithIntList :: [Integer] -> [Integer]
testMyReverseWithIntList l = map natToInteger $ withSomeVect (listToSomeVect . map integerToNat $ l) (\sn -> vectToList . myReverse) 
{-| ghci: 
*Part2.Sez10_2aVect> testMyReverseWithIntList [1..9]
[9,8,7,6,5,4,3,2,1]
 -}


{- 
Problems with just using `SNat n` evidence in proofs.
This would give me a chance of linear cost algorithm!
 
zeroSizeIsVNil :: forall (v :: Vect 'Z a) . v :~~: 'VNil
zeroSizeIsVNil = undefined

vappendVNilRightNeutral' :: forall (n :: Nat) (v :: Vect n a) . SNat n -> (VAppend v 'VNil) :~~: v
vappendVNilRightNeutral' SZ = case zeroSizeIsVNil of HRefl -> vappendVNilRightNeutral SVNil
vappendVNilRightNeutral' (SS k) = undefined

Results in: 
  -- • Could not deduce: v ~ 'VNil
  --     from the context: n1 ~ 'Z
-}
