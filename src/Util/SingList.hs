
{-# LANGUAGE TemplateHaskell
      , KindSignatures
      , DataKinds
      , GADTs
      , PolyKinds
      , TypeInType 
      , TypeOperators 
      , TypeFamilies
      , StandaloneDeriving
      , UndecidableInstances 
      , ScopedTypeVariables
      , TypeSynonymInstances
#-}
module Util.SingList where
import Data.Singletons.TH

$(singletons [d|
  data List a = LNil | LCons a (List a) deriving Show

  append :: List a -> List a -> List a
  append LNil ys = ys
  append (LCons x xs) ys = LCons x (append xs ys)

  oneElem :: a -> List a
  oneElem a = LCons a LNil
  |])


  
