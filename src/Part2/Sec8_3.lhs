|Markdown version of this file: https://github.com/rpeszek/IdrisTddNotes/wiki/idrVsHs_Part2_Sec8_3
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
>    TemplateHaskell
>   , TypeOperators
>   , GADTs
>   , TypeFamilies
>   , DataKinds
>   , PolyKinds
>   , KindSignatures
>   , EmptyCase
>   , TypeSynonymInstances -- needed for DecEq instance of singletons SNat
>   , ScopedTypeVariables -- singletons need it
>   -- , TypeInType
>   , UndecidableInstances -- fancy DecEq instance for MyPair needs it
> #-}
> {-# OPTIONS_GHC -fwarn-incomplete-patterns #-}
>
> module Part2.Sec8_3 where
> import Data.Type.Equality
> import Data.Kind (Type)
> import Data.Void
> import qualified Util.NonLitsNatAndVector as V1
> import qualified Util.SingVector as V2
> import Data.Singletons
> import Data.Singletons.TH
>
> data Dec (prop :: Type) where
>    Yes :: prop -> Dec prop
>    No  :: (prop -> Void) -> Dec prop
>
> instance Show (Dec a) where
>   show (Yes _) = "Yes"
>   show (No _) = "No"
>
> class DecEq (ty :: k -> Type) where
>      decEq :: ty a -> ty b -> Dec (ty a :~: ty b)

`exactLength` and `DecEq` for `Nat` example
-------------------------------------------

> congSS :: (V1.SNat n :~: V1.SNat m) -> (V1.SNat ('V1.S n) :~: V1.SNat ('V1.S m))
> congSS Refl = Refl
>
> revSS :: (V1.SNat ('V1.S n) :~: V1.SNat ('V1.S m)) -> (V1.SNat n :~: V1.SNat m)
> revSS Refl = Refl
>
> {-! Empty case match -}
> zSIsNotSS :: V1.SNat n -> (V1.SNat 'V1.Z :~: V1.SNat ('V1.S n)) -> Void
> zSIsNotSS _ x = case x of { }
>
> instance DecEq V1.SNat where
>      decEq V1.SZ V1.SZ = Yes Refl
>      decEq V1.SZ (V1.SS k) = No $ zSIsNotSS k
>      decEq (V1.SS k) V1.SZ = No $ zSIsNotSS k . sym
>      decEq (V1.SS k1) (V1.SS k2) = let recv = decEq k1 k2
>                               in case recv of 
>                                   Yes prf -> Yes $ congSS prf
>                                   No contra -> No $ contra . revSS
>
> exactLength :: V1.SNat len -> V1.Vect m a -> Maybe (V1.Vect len a) 
> exactLength len vect = case decEq (V1.vlength vect) len of
>         Yes Refl -> Just vect
>         No _ -> Nothing

ghci:
```
*Part2.Sec8_3> exactLength (SS SZ) $ "t" :::  Nil
Just ("t" ::: Nil)
```
The `singletons` version is identical (note the fancy instance declaration that Haskell accepts)

> congSS' :: (V2.SNat n :~: V2.SNat m) -> (V2.SNat ('V2.S n) :~: V2.SNat ('V2.S m))
> congSS' Refl = Refl
>
> revSS' :: (V2.SNat ('V2.S n) :~: V2.SNat ('V2.S m)) -> (V2.SNat n :~: V2.SNat m)
> revSS' Refl = Refl
>
> zSIsNotSS' :: V2.SNat n -> (V2.SNat 'V2.Z :~: V2.SNat ('V2.S n)) -> Void
> zSIsNotSS' _ x = case x of { }
>
> instance DecEq (Sing :: V2.Nat -> Type) where
>      decEq V2.SZ V2.SZ = Yes Refl
>      decEq V2.SZ (V2.SS k) = No $ zSIsNotSS' k
>      decEq (V2.SS k) V2.SZ = No $ zSIsNotSS' k . sym
>      decEq (V2.SS k1) (V2.SS k2) = let recv = decEq k1 k2
>                               in case recv of 
>                                   Yes prf -> Yes $ congSS' prf
>                                   No contra -> No $ contra . revSS'

The above instance could be replaced with `instance DecEq V2.SNat where`.   
ghci:
```
*Part2.Sec8_3> :info V2.SNat
type V2.SNat = Sing :: V2.Nat -> *
```

`MyPair` example
----------------

`DecEq` instance for `MyPair` is harder because I need type level representation of
constituent values.  Possible direction is to define `decEq` as type family as in [idrVsHs_Part2_Sec9_1].
But the following works and is closer to Idris

> -- Note, compilation errors when generating singletons for data MyPair a b = MkMyPair a b 
> -- if I try deriving Eq
> $(singletons [d|
>  data MyPair a b = MkMyPair a b deriving (Show)
>  |])

Note:
```
*Part2.Sec8_3> :t SMkMyPair
SMkMyPair
  :: forall b a (n1 :: a) (n2 :: b).
     Sing n1 -> Sing n2 -> Sing ('MkMyPair n1 n2)
```
And Haskell allows me to express this nicely, the code is almost identical to Idris:

> instance (DecEq (Sing :: a -> Type), DecEq (Sing :: b -> Type)) => DecEq (Sing :: MyPair a b -> Type) where
>    decEq (SMkMyPair a1 b1) (SMkMyPair a2 b2) = case decEq a1 a2 of 
>         Yes Refl -> case decEq b1 b2 of
>             Yes Refl -> Yes Refl
>             No contra -> No (secondUnequal Refl contra)
>         No contra -> No (firstUnequal contra)
>
> firstUnequal :: ((Sing a1 :~: Sing a2) -> Void) -> (Sing (MkMyPair a1 b1) :~: Sing (MkMyPair a2 b2)) -> Void
> firstUnequal contra Refl = contra Refl
>
> secondUnequal :: (Sing a1 :~: Sing a2) -> ((Sing b1 :~: Sing b2) -> Void) ->  (Sing (MkMyPair a1 b1) :~: Sing (MkMyPair a2 b2)) -> Void
> secondUnequal Refl contra Refl = contra Refl

This is all very similar to Idris!
Except, in Haskell, I have to work with `ty :: k -> Type` mappings (like `SNat`) instead of directly working with `ty` (`Nat`).

ghci:
```
*Part2.Sec8_3> decEq (SMkMyPair V2.SZ (V2.SS V2.SZ)) (SMkMyPair V2.SZ (V2.SS V2.SZ))
Yes
*Part2.Sec8_3> decEq (SMkMyPair V2.SZ (V2.SS V2.SZ)) (SMkMyPair V2.SZ V2.SZ)
No
```
