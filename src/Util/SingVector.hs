{-
TODO Seems like 8.0 version has problems with defining opertions like plus
-}

{-# LANGUAGE TemplateHaskell
      , KindSignatures
      , DataKinds
      , GADTs
      , PolyKinds
  --  , TypeInType
  --  , TypeOperators 
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

test :: SNat s -> ()
test = undefined
