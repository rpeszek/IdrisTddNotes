|Markdown version of this file: https://github.com/rpeszek/IdrisTddNotes/wiki/idrVsHs_Part2_Sec5_3_3
|Idris Src: Sec5_3_3.idr

Section 5.3.3. Dependent Pair vs Haskell
========================================

Idris code example
------------------  
|IdrisRef: Sec5_3_3.idr 

Compared to Haskell
-------------------
This follows the idea from 5.3.2.

> {-# LANGUAGE DeriveFunctor
>    , StandaloneDeriving
>    , GADTs
>    , KindSignatures
>    , DataKinds
>    , TypeOperators 
>    , ScopedTypeVariables
> #-}
> module Part2.Sec5_3_3 where
> import GHC.TypeLits
> import Part2.Sec3_2_3 (Vect(..))
> import Data.Proxy
>
> {-| 
>  Provides link between Nat types and values.
>  SNat allows to lift from value n to type n.
>  Note: using predecessor (n - 1) instead of (1 + n) seems, in some cases, 
>  to work better see Part2.Sec6_2_1 
> -}
> data SNat (n :: Nat) where
>  SZ :: SNat 0
>  SS :: SNat n -> SNat (1 + n)
>
> deriving instance Show (SNat n) 
>
> data VectUnknown a where 
>    MkVect :: SNat n -> Vect n a -> VectUnknown a 
>  
> deriving instance Show a => Show (VectUnknown a) 
>
> listToVect :: [a] -> VectUnknown a
> listToVect [] = MkVect SZ Nil
> listToVect (x : xs) = 
>              let forXs = listToVect xs
>              in case forXs of
>              MkVect nx forXsV -> MkVect (SS nx) (x ::: forXsV) 

ghci:
```
*Part2.Sec5_3_3> listToVect [1,2,3]
MkVect (SS (SS (SS SZ))) (1 ::: (2 ::: (3 ::: Nil)))
*Part2.Sec5_3_3> 
```
