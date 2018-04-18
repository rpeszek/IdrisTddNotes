{- 
   Singletons version of Sec6_3 code (type safe schema store).
   Singletons are used to generate kind/type level represenations for Nat and Schema types
   removing some boilerplate I had to do in Sec6_3
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
import Util.SingVector (Vect(..), Nat(..), SNat(..), Sing(..), someNatToInteger) 
import Data.ByteString (ByteString)
import qualified Data.ByteString.Char8 as CH8
import Util.AttoparsecUtil (optional, spaces, between, parseAll)
import Data.Attoparsec.ByteString.Char8 (Parser, decimal, string, char) 
import Part2.Sec6_3 (replWith)

 
$(singletons [d|
 data Schema = SString
              | SInt
              | SCons Schema Schema
                deriving Show

 |])

{- 
Note
 type SSchema = Sing :: Schema -> * 
 I am using SSchema instead of just Sing
 this seems easier to use and it disambiguates compilation issues

 for Nat polymorphic Sing worked just fine.
-}

-- unchanged other than use of `SCons` instead of `:+`
type family SchemaType  (sch :: Schema) :: Type where
   SchemaType 'SString = ByteString
   SchemaType 'SInt = Int
   SchemaType (x `SCons` y) = (SchemaType x, SchemaType y)

testST :: SchemaType ('SInt `SCons` 'SString `SCons` 'SInt)
testST = undefined

-- unchanged
data Command (sch :: Schema) where
            -- SetSchema is polymorphic in schema type
            SetSchema :: SSchema asch -> Command sch
            Add :: SchemaType sch -> Command sch
            Get :: Int -> Command sch
            Quit :: Command sch

-- AnySchema handling unchanged, needed to swap schema
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

-- unchanged except for use of polymorphic Sing 
data DataStore (sch :: Schema) where
  MkDataStore :: SSchema sc -> Sing n -> Vect n (SchemaType sc) -> DataStore sc

{- helper methods used with DataStore -}

{-| This one maps to just schema in Idris which is overloaded name -}
getSchema :: DataStore sch -> SSchema sch 
getSchema (MkDataStore sch _ _) = sch

{-| SomeSing Nat plays role of UnknownNat 
`toSing . fromSing` moves between SNat and SomeSing Nat -}
size :: DataStore sch -> SomeSing Nat
size (MkDataStore _ size _) = toSing . fromSing $ size

-- unchanged
display :: SSchema sch -> SchemaType sch -> ByteString
display SSString item = item
display SSInt item =  CH8.pack . show $ item
display (SSCons sch1 sch2) (item1, item2) = display sch1 item1 <> " " <> display sch2 item2
 
getvelem :: Int -> Vect n a -> Maybe a
getvelem _ Nil = Nothing
getvelem 0 (x ::: _) = Just x
getvelem i (_ ::: xs) = getvelem (i - 1) xs

retrieve :: Int -> DataStore sch -> Maybe (SchemaType sch)
retrieve pos (MkDataStore _ _ vect) = getvelem pos vect

getEntry :: Int -> DataStore sch -> Maybe ByteString 
getEntry pos store@(MkDataStore ss _ vect)  = 
      if pos < 0
      then Just ("Out of range") 
      else case retrieve pos store of
         Nothing -> Just "Out of range"
         Just rec  -> Just (display ss rec)

-- slight diff in pattern match using SomeSing SZ
setSchema :: DataStore asch -> SSchema sch -> Maybe (DataStore sch)
setSchema store schema = case size store of
         SomeSing SZ -> Just (MkDataStore schema SZ Nil)
         _  -> Nothing 

-- unchanged
addToStore :: DataStore sc -> SchemaType sc -> DataStore sc
addToStore (MkDataStore schema size elems) newitem
          = MkDataStore schema (SS size) (addToData schema newitem size elems)
  where
    -- I had to bring type level schema and size evidence to make it work
    -- Couldn't match type ‘n’ with ‘(n + 1) - 1’ when using Part2.Sec6_2_1 definitions
    addToData ::  SSchema sc -> SchemaType sc -> Sing oldsize -> Vect oldsize (SchemaType sc) -> Vect ('S oldsize) (SchemaType sc)
    addToData schema newitem SZ Nil = newitem ::: Nil
    addToData schema newitem (SS n) (item ::: items) = item ::: addToData schema newitem n items

{- parser logic is the same -}

sstring :: Parser Schema 
sstring =  string "String" *> pure SString

sint :: Parser Schema
sint = string "Int" *> pure SInt

scolumn :: Parser Schema
scolumn = sstring <|> sint

schemaBody :: Parser Schema 
schemaBody = do  
    col  <- scolumn
    _    <- optional spaces
    rest <- optional schemaBody
    case rest of
       Nothing ->  pure col
       Just rest -> pure (col `SCons` rest)

schema :: Parser Schema 
schema = string "schema" *> spaces *> schemaBody

schemaTypeBody :: SSchema sch -> Parser (SchemaType sch)
schemaTypeBody SSString = between (char '"') (char '"')
schemaTypeBody SSInt = decimal
schemaTypeBody (schemal `SSCons` schemar) = do
               parsed1 <- schemaTypeBody schemal
               _    <- spaces
               parsed2 <- schemaTypeBody schemar
               return (parsed1, parsed2)

schemaType :: SSchema sch -> Parser (SchemaType sch)
schemaType sch = string "add" *> spaces *> schemaTypeBody sch
{- end parser logic -}


-- unchanged
command :: SSchema sc -> Parser (Command sc)
command sc = schemaToSchemaCmd <$> schema <|>
            (string "quit" *> pure Quit) <|>
            (string "get") *> spaces *> (Get <$> decimal) <|>
            (Add <$> schemaType sc)

{-| 
  Haskell naming conventions seems to prefer SomeDataStore, I am using Idris book 
  convention here.
-}
data UnknownDataStore where
 MkUnknownStore :: DataStore sc -> UnknownDataStore

processInput :: UnknownDataStore -> ByteString -> Maybe (ByteString, UnknownDataStore)
processInput (MkUnknownStore store) input 
         =  let ss = getSchema store
            in case parseAll (command ss) input of
                Left msg -> Just ("Invalid command: " <> CH8.pack msg, MkUnknownStore store)
                Right (Add item) ->
                   Just ("ID " <> CH8.pack ( show (someNatToInteger . size $ store)), MkUnknownStore $ addToStore store item)
                Right (Get pos) -> (\s -> (s, MkUnknownStore store)) <$> getEntry pos store
                Right (SetSchema schema') -> case setSchema store schema' of
                       Nothing -> Just ("Can't update schema", MkUnknownStore store)
                       Just store' -> Just ("OK", MkUnknownStore store')
                Right Quit -> Nothing

initDs :: DataStore 'SString
initDs = MkDataStore SSString SZ Nil

sec6_3sing :: IO ()
sec6_3sing = replWith (MkUnknownStore initDs) "Command: " processInput
