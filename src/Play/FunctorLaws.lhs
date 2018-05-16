|Markdown version of this file: https://github.com/rpeszek/IdrisTddNotes/wiki/idrVsHs_Play_FunctorLaws
|Idris Src: FunctorLaws.idr

VerifiedFunctor in Idris and Haskell
=====================================
Ref: https://www.schoolofhaskell.com/user/edwardk/snippets/fmap  
__Note the above reference, checking second functor law is redundant.__


Idris code example
------------------  
|IdrisRef: FunctorLaws.idr 


Compared to Haskell
-------------------
Ref: https://blog.jle.im/entry/verified-instances-in-haskell.html

> {-# LANGUAGE TemplateHaskell
>       , KindSignatures
>       , DataKinds
>       , GADTs
>       , PolyKinds
>       , TypeInType 
>       , TypeOperators 
>       , TypeFamilies
>       , StandaloneDeriving
>       , UndecidableInstances 
>       , ScopedTypeVariables
>       , LambdaCase
> #-}
> module Play.FunctorLaws where
> 
> import Data.Singletons.TH
> import Data.Promotion.Prelude.Function
> import Data.Type.Equality
> import Prelude hiding (Maybe)

Note there is no straightforward way to correlate value level map with type level Map so
`VerifiedFunctor f` does not extend `Functor f` like it does in Idris.

> class VerifiedFunctor f where
> 
>     type Fmap a b (g :: a ~> b) (x :: f a) :: f b
> 
>     sFmap
>         :: Sing (g            :: a ~> b)
>         -> Sing (x            :: f a   )
>         -> Sing (Fmap a b g x :: f b   )
> 
>     -- | fmap id x == x
>     identityLaw
>         :: Sing (x :: f a)
>         -> Fmap a a IdSym0 x :~: x
 
`distLaw` is much less readable than in Idris. I have 
changed order of args for convenience.  Here is the legend that helps
reading the scary `(((:.$) @@ g) @@ h) x`:

* `type (~>) a b = TyFun a b -> Type` 
* `type (@@) (a :: k1 ~> k) (b :: k1) = Apply a b :: k`
* `(:.$) :: (b ~> c) ~> ((a ~> b) ~> (a ~> c))`

>     {- | fmap f (fmap g x) = fmap (f . g) x -}
>     distLaw
>         :: Sing (g :: b ~> c)
>         -> Sing (h :: a ~> b)
>         -> Sing (x :: f a   )
>         -> Fmap b c g (Fmap a b h x) :~: Fmap a c (((:.$) @@ g) @@ h) x

Instead of using Data.SingBased.List I am redefining it here for clarity:

>
> $(singletons [d|
>   data List a = LNil | LCons a (List a) deriving Show
>   infixr 9 `LCons`
> 
>   map :: (a -> b) -> List a -> List b
>   map f LNil = LNil
>   map f (LCons x xs) = LCons (f x) (map f xs)
>  |])
>
> instance VerifiedFunctor List where
> 
>     type Fmap a b g x = Map g x
> 
>     sFmap = sMap
> 
>     identityLaw = \case
>       SLNil       -> Refl
>       SLCons _ xs ->
>         case identityLaw xs of
>           Refl -> Refl
> 
>     distLaw g h = \case
>       SLNil -> Refl
>       SLCons _ xs ->
>         case distLaw g h xs of
>           Refl -> Refl
  
Same for `Maybe`:

>
> $(singletons [d|
>   data Maybe a = Nothing | Just a deriving Show
> 
>   maybeMap :: (a -> b) -> Maybe a -> Maybe b
>   maybeMap f Nothing = Nothing
>   maybeMap f (Just x) = Just (f x)
>  |])
>
> instance VerifiedFunctor Maybe where
> 
>     type Fmap a b g x = MaybeMap g x
> 
>     sFmap = sMaybeMap
> 
>     identityLaw = \case
>       SNothing       -> Refl
>       SJust x        -> Refl
> 
>     distLaw g h = \case
>       SNothing -> Refl
>       SJust x  -> Refl

Idris wins. Keeping the value level syntax is huge! 
