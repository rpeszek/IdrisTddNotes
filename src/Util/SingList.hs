
{-# LANGUAGE TemplateHaskell
      , KindSignatures
      , DataKinds
      , GADTs
      , PolyKinds
      , TypeInType 
      , TypeOperators 
      , TypeFamilies
      , UndecidableInstances 
      , ScopedTypeVariables
      , TypeSynonymInstances
      , FlexibleContexts
#-}
module Util.SingList where
import Data.Singletons.TH
import Data.Singletons.Prelude
import Data.Ord

$(singletons [d|
  data List a = LNil | LCons a (List a) deriving Show
  infixr 9 `LCons`

  append :: List a -> List a -> List a
  append LNil ys = ys
  append (LCons x xs) ys = LCons x (append xs ys)
  infixr 9 `append`

  oneElem :: a -> List a
  oneElem a = LCons a LNil

  (.>) :: a -> List a -> List a
  (.>) = LCons
  infixr 5 .>

  lToList :: [a] -> List a
  lToList [] = LNil 
  lToList (x: xs) = LCons x (lToList xs)

  |])

-- errors our if placed inside $(singletons ..)  seems like singletons, basically, has problems with syntax sugar
listToL :: List a -> [a]
listToL LNil = []
listToL (LCons x xs) = x : (listToL xs)

withList :: [a] -> (List a -> r) -> r
withList xs f = f (lToList xs)

-- merge does not want to lift (see Sec10_1 for implementation that returns SomeSing (List a) )
merge :: (Ord a) => List a -> List a -> List a
merge LNil ys = ys
merge xs LNil = xs
merge (LCons x xs) (LCons y ys) 
        = let (first, second) = case compare x y of
                LT -> (x, y)
                _  -> (y, x)
          in first `LCons` second `LCons` (merge xs ys) 


(.>>) :: Sing n1 -> Sing n2 -> Sing ('LCons n1 n2)
(.>>) = SLCons
infixr 5 .>>
