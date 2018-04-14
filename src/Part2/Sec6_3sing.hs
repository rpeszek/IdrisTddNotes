{- 
   Singletons version of Sec6_3, type safe schema store.
   Work in progress 
-}

{-# LANGUAGE 
    StandaloneDeriving
   , GADTs
   , KindSignatures
   , DataKinds
   , TypeOperators 
   , TypeFamilies
   , ScopedTypeVariables
   , OverloadedStrings
   , AllowAmbiguousTypes 
   , UndecidableInstances
   , TemplateHaskell
#-}
{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}

module Part2.Sec6_3sing where
import Data.Singletons.TH
import Control.Applicative ((<|>))
import Data.Monoid ((<>))
import Data.Kind (Type)
-- import Util.NonLitsNatAndVector (Vect(..), Nat(..), SNat(..), UnknownNat(..), sNatToUnknownNat, unknownNatToInteger)
import Data.ByteString (ByteString)
import qualified Data.ByteString as B
import Data.ByteString.Char8 ()
import qualified Data.ByteString.Char8 as CH8
import Data.Attoparsec.ByteString hiding (takeTill)
import Data.Attoparsec.ByteString.Char8 
import Prelude hiding (getLine, putStrLn)

 
$(singletons [d|
 data Schema = SString
              | SInt
              | (:+) Schema Schema
               deriving Show

 |])

 
type family SchemaType  (sch :: Schema) :: Type where
   SchemaType 'SString = ByteString
   SchemaType 'SInt = Int
   SchemaType (x :+ y) = (SchemaType x, SchemaType y)

testST :: SchemaType ('SInt :+ 'SString :+ 'SInt)
testST = undefined

data Command (sch :: Schema) where
            -- SetSchema is polymorphic in schema type
            SetSchema :: Sing asch -> Command sch
            Add :: SchemaType sch -> Command sch
            Get :: Int -> Command sch
            Quit :: Command sch
