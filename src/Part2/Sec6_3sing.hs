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
              | SCons Schema Schema
                deriving Show

 |])

t :: Schema -> Schema -> Schema
t s1 s2 = undefined
-- (:+++) :: Schema -> Schema -> Schema
-- (:+++) = SCons
-- infixr 5 :+++

 
type family SchemaType  (sch :: Schema) :: Type where
   SchemaType 'SString = ByteString
   SchemaType 'SInt = Int
   SchemaType (x `SCons` y) = (SchemaType x, SchemaType y)

testST :: SchemaType ('SInt `SCons` 'SString `SCons` 'SInt)
testST = undefined

data Command (sch :: Schema) where
            -- SetSchema is polymorphic in schema type
            SetSchema :: SSchema asch -> Command sch
            Add :: SchemaType sch -> Command sch
            Get :: Int -> Command sch
            Quit :: Command sch

data AnySchema (sch :: Schema) where
            MkAnySchema :: SSchema asch -> AnySchema sch

toAnySchema :: Schema -> AnySchema sch
toAnySchema SString = MkAnySchema SSString
toAnySchema SInt = MkAnySchema SSInt
toAnySchema (s1 `SCons` s2) = 
      case toAnySchema s1 of
        MkAnySchema s1' -> case toAnySchema s2 of 
          MkAnySchema s2' ->
            MkAnySchema $ SSCons s1' s2'

toSetSchemaCommand :: AnySchema sch -> Command sch
toSetSchemaCommand (MkAnySchema x) = SetSchema x

schemaToSchemaCmd :: Schema -> Command sch 
schemaToSchemaCmd  = toSetSchemaCommand . toAnySchema
