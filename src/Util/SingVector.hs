{-
TODO Seems like 8.0 version has problems with defining opertions like plus
-}

{-# LANGUAGE TemplateHaskell
      , KindSignatures
      , DataKinds
      , GADTs
      , PolyKinds
      , TypeInType -- needed for SVect
      , TypeOperators 
      , TypeFamilies
   -- , StandaloneDeriving
      , UndecidableInstances 
      , ScopedTypeVariables
#-}

module Util.SingVector where
import Data.Singletons.TH

$(singletons [d|
  data Nat = Z | S Nat
    deriving (Show, Eq)

  plus :: Nat -> Nat -> Nat
  plus Z m = m
  plus (S n) m = S (plus n m)
  |])

data Vect (n :: Nat) a where
     Nil :: Vect 'Z a
     (:::) :: a -> Vect n a -> Vect ('S n) a
infixr 5 :::

-- TODO is there a more singleton version of this?
someNatToInteger :: SomeSing Nat -> Integer
someNatToInteger (SomeSing SZ) = 0
someNatToInteger (SomeSing (SS k)) = 1 + someNatToInteger (SomeSing k)

test :: SNat s -> ()
test = undefined

-- Currently, I do not know how to do singletons for the Vect itself

data SVect (v :: Vect n a) where
  SNil :: SVect  'Nil
  SCons :: Sing a -> SVect xs -> SVect (a '::: xs)
