|Markdown version of this file: https://github.com/rpeszek/IdrisTddNotes/wiki/idrVsHs_Part2_Sec8_2
|Idris Src: Sec8_3.idr

Section 8.3 Dec/DecEq vs Haskell
================================
This note is about Idris Dec type and DecEq interface and mimicking these in Haskell.

Idris code example
------------------  
|IdrisRef: Sec8_3.idr 

Compared to Haskell
-------------------

> {-# LANGUAGE 
>     TypeOperators
>   , GADTs
>   , TypeFamilies
>   , DataKinds
>   , PolyKinds
>   -- , ScopedTypeVariables
>   , KindSignatures
> #-}
> {-# OPTIONS_GHC -fwarn-incomplete-patterns #-}
>
> module Part2.Sec8_3 where
> import Data.Type.Equality
> import Data.Kind (Type)
> import Data.Void
> import Util.NonLitsNatAndVector
>
> data Dec (prop :: Type) where
>    Yes :: prop -> Dec prop
>    No  :: (prop -> Void) -> Dec prop
>
> class DecEq (ty :: k -> Type) where
>      decEq :: ty a -> ty b -> Dec (ty a :~: ty b)
>
> congSS :: (SNat n :~: SNat m) -> (SNat ('S n) :~: SNat ('S m))
> congSS Refl = Refl
>
> revSS :: (SNat ('S n) :~: SNat ('S m)) -> (SNat n :~: SNat m)
> revSS Refl = Refl
>
> {-| 
>  There is no impossible keyword in Haskell
>  To avoid: The type signature for ‘zSIsNotSS’ lacks an accompanying binding
>  I need something, Empty pattern match is not accepted
> -}
> zSIsNotSS :: SNat n -> (SNat 'Z :~: SNat ('S n)) -> Void
> zSIsNotSS = undefined
>
> instance DecEq SNat where
>      decEq SZ SZ = Yes Refl
>      decEq SZ (SS k) = No $ zSIsNotSS k
>      decEq (SS k) SZ = No $ zSIsNotSS k . sym
>      decEq (SS k1) (SS k2) = let recv = decEq k1 k2
>                               in case recv of 
>                                   Yes prf -> Yes $ congSS prf
>                                   No contra -> No $ contra . revSS
>
> exactLength :: SNat len -> Vect m a -> Maybe (Vect len a) 
> exactLength len vect = case decEq (vlength vect) len of
>         Yes Refl -> Just vect
>         No _ -> Nothing

ghci:
```
*Part2.Sec8_3> exactLength (SS SZ) $ "t" :::  Nil
Just ("t" ::: Nil)
```
Mimicking of MyPair would be harder because I would need type level representation of
constituent values.
