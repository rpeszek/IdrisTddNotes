|Markdown version of this file: https://github.com/rpeszek/IdrisTddNotes/wiki/Part2_Sec8_3_deceq
|Idris Src: Sec8_3_deceq.idr

Section 8.3 Dec/DecEq vs Haskell
================================
This note is about Idris Dec type and DecEq interface and mimicking these in Haskell.

Idris code example
------------------  
|IdrisRef: Sec8_3_deceq.idr 

Compared to Haskell
-------------------
I currently have 2 implementations of `Nat` and `Vect`
 * by hand `Data.CodedByHand`
 * partially using `singletons` `Data.SingBased`

Both are equivalent, moving forward, I will focus on the second

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
> {-# OPTIONS_GHC -fwarn-unused-imports #-}
>
> module Part2.Sec8_3_deceq where
> import Data.Type.Equality
> import Data.Kind (Type)
> import Data.Void
> import Data.SingBased (Nat(..), Vect(..), vlength, type SNat, type Sing(..))
> import Data.Singletons
> import Data.Singletons.TH
> import Data.Bifunctor

`DecEq` 
------

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
>

`DecEq` for `Nat` 
----------------

> instance DecEq (Sing :: Nat -> Type) where
>      decEq SZ SZ = Yes Refl
>      decEq SZ (SS k) = No $ zSIsNotSS k
>      decEq (SS k) SZ = No $ zSIsNotSS k . sym
>      decEq (SS k1) (SS k2) = let recv = decEq k1 k2
>                               in case recv of 
>                                   Yes prf -> Yes $ congSS prf
>                                   No contra -> No $ contra . revSS
>
> congSS :: (SNat n :~: SNat m) -> (SNat ('S n) :~: SNat ('S m))
> congSS Refl = Refl
>
> revSS :: (SNat ('S n) :~: SNat ('S m)) -> (SNat n :~: SNat m)
> revSS Refl = Refl
>
> zSIsNotSS :: SNat n -> (SNat 'Z :~: SNat ('S n)) -> Void
> zSIsNotSS _ x = case x of { }

ghci:
```
*Part2.Sec8_3_deceq> decEq s1 s2
No
*Part2.Sec8_3_deceq> decEq s1 s1
Yes
```
The above instance could be replaced with `instance DecEq SNat where ...`.   
ghci:
```
*Part2.Sec8_3_deceq> :info SNat
type SNat = Sing :: Nat -> *
```

`exactLength` example
---------------------

> exactLength :: SNat len -> Vect m a -> Maybe (Vect len a) 
> exactLength len vect = case decEq (vlength vect) len of
>         Yes Refl -> Just vect
>         No _ -> Nothing

ghci:
```
*Part2.Sec8_3_deceq> exactLength (SS SZ) $ "t" :::  VNil
Just ("t" ::: VNil)
```


`SingKind` version of `DecEq`
-----------------------------

I am having more luck with the following approach to `DecEq`:

> class SingKind k => DecEqSing k where
>      decEqSing :: forall (a :: k) (b :: k) . Sing a -> Sing b -> Dec (Sing a :~: Sing b)
>
> instance DecEqSing (Nat) where
>      decEqSing SZ SZ = Yes Refl
>      decEqSing SZ (SS k) = No $ zSIsNotSS k
>      decEqSing (SS k) SZ = No $ zSIsNotSS k . sym
>      decEqSing (SS k1) (SS k2) = let recv = decEqSing k1 k2
>                               in case recv of 
>                                   Yes prf -> Yes $ congSS prf
>                                   No contra -> No $ contra . revSS

ghci:
```
*Part2.Sec8_3_deceq> decEqSing s1 s2
No
*Part2.Sec8_3_deceq> decEqSing s1 s1
Yes
```

`MyPair` example
----------------

`DecEq` instance for `MyPair` is harder because I need type level representation of
constituent values.  Possible direction is to define `decEq` as type family as in [Part2_Sec9_1_elem](Part2_Sec9_1_elem).
But the following works and is closer to Idris

> -- Note, compilation errors when generating singletons for data MyPair a b = MkMyPair a b 
> -- if I try deriving Eq
> $(singletons [d|
>  data MyPair a b = MkMyPair a b deriving (Show)
>  |])
>
> {-| needed for convenience later on -}
> instance Bifunctor MyPair where
>   bimap fab fcd (MkMyPair a c) = MkMyPair (fab a) (fcd c)


Note:
```
*Part2.Sec8_3_deceq> :t SMkMyPair
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
> instance (DecEqSing a, DecEqSing b) => DecEqSing (MyPair a b) where
>    decEqSing (SMkMyPair a1 b1) (SMkMyPair a2 b2) = case decEqSing a1 a2 of 
>         Yes Refl -> case decEqSing b1 b2 of
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
*Part2.Sec8_3_deceq> decEq (SMkMyPair SZ (SS SZ)) (SMkMyPair SZ (SS SZ))
Yes
*Part2.Sec8_3_deceq> decEq (SMkMyPair SZ (SS SZ)) (SMkMyPair SZ SZ)
No
*Part2.Sec8_3_deceq> decEqSing (SMkMyPair SZ (SS SZ)) (SMkMyPair SZ (SS SZ))
Yes
*Part2.Sec8_3_deceq> decEqSing (SMkMyPair SZ (SS SZ)) (SMkMyPair SZ SZ)
No
```
