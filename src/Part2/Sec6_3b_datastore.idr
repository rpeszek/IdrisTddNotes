module Part2.Sec6_3b_datastore
import Data.Vect
import Util.MiniParser

%default total 

infixr 5 .+.

||| ADT that represents parsed schema
data Schema = SString
            | SInt
            | (.+.) Schema Schema

||| Type level function that maps Schema to actual type, composite schema
||| is mapped to a tuple.
SchemaType : Schema -> Type
SchemaType SString = String
SchemaType SInt = Int
SchemaType (x .+. y) = (SchemaType x, SchemaType y)

{-
idris repl:
*src/Part2/Sec6_3_datastore> SchemaType (SInt .+. SString .+. SInt)
(Int, String, Int) : Type
-}     

{- This needs schema type parameter to cary the schema information around -}
||| Type representing user commands (DSL) 
data Command : Schema -> Type where
           -- works in context of old schema, polymorphic in the return type
           SetSchema : (newschema : Schema) -> Command schema
           Add : SchemaType schema -> Command schema
           Get : Integer -> Command schema
           Quit : Command schema

record DataStore where
       constructor MkData
       schema : Schema
       size : Nat
       items : Vect size (SchemaType schema)

{- 
teststore = MkData (SInt .+. SString .+. SInt) 1 [(2, "Two", 42)]
-}

{- helper methods used with DataStore -}

addToStore : (store : DataStore) -> SchemaType (schema store) -> DataStore
addToStore (MkData schema size store) newitem
           = MkData schema _ (addToData store)
  where
    addToData : Vect oldsize (SchemaType schema) -> Vect (S oldsize) (SchemaType schema)
    addToData [] = [newitem]
    addToData (item :: items) = item :: addToData items

display : SchemaType schema -> String
display {schema = SString} item = show item
display {schema = SInt} item = show item
display {schema = (x .+. y)} (iteml, itemr)
            = display iteml ++ ", " ++ display itemr


{- Changed from the book version to emphasize type safe retrieval -}
retrieve : (pos : Integer) -> (store : DataStore) -> Maybe (SchemaType (schema store))
retrieve pos store =
      integerToFin pos (size store) >>= (\i => pure (index i (items store)))

getEntry : (pos : Integer) -> (store : DataStore) -> Maybe (String, DataStore)
getEntry pos store = case retrieve pos store of
             Nothing => Just ("Out of range\n", store)
             Just rec => Just ((display rec) ++ "\n", store)


setSchema : (store : DataStore) -> Schema -> Maybe DataStore
setSchema store schema = case size store of
       Z => Just (MkData schema _ [])
       S k => Nothing

{- Parsers -}
sstring : Parser Schema 
sstring =  string "String" *> pure SString

sint : Parser Schema
sint = string "Int" *> pure SInt

scolumn : Parser Schema
scolumn = sstring <|> sint

covering
schemaBody : Parser Schema 
schemaBody = do  
     col  <- scolumn
     _    <- optional spaces
     rest <- optional schemaBody
     case rest of
        Nothing =>  pure col
        Just rest => pure (col .+. rest)

{- Note Idris has no problem with this name being overloaded -}
covering
schema : Parser Schema 
schema = string "schema" *> spaces *> schemaBody

covering
schemaTypeBody : (sch : Schema) -> Parser (SchemaType sch)
schemaTypeBody SString = between (char '"') (char '"')
schemaTypeBody SInt = decimalInt
schemaTypeBody (schemal .+. schemar) = do
                parsed1 <- schemaTypeBody schemal
                _    <- spaces
                parsed2 <- schemaTypeBody schemar
                pure (parsed1, parsed2)

covering
schemaType : (sch : Schema) -> Parser (SchemaType sch)
schemaType sch = string "add" *> spaces *> schemaTypeBody sch
                              
covering
command : (sc : Schema) -> Parser (Command sc)
command sc = (SetSchema <$> schema) <|>
             (string "quit" *> pure Quit) <|>
             (string "get") *> spaces *> (Get <$> decimalInteger) <|>
             (Add <$> schemaType sc)

{- End Parsers -}

||| replWith implementation method
covering
processInput : DataStore -> String -> Maybe (String, DataStore)
processInput store input
          = case parseAll (command (schema store)) input of
                 Left msg => Just ("Invalid command: " ++ msg ++ "\n", store)
                 Right (Add item) =>
                    Just ("ID " ++ show (size store) ++ "\n", addToStore store item)
                 Right (Get pos) => getEntry pos store
                 Right (SetSchema schema') => case setSchema store schema' of
                        Nothing => Just ("Can't update schema\n", store)
                        Just store' => Just ("OK\n", store')
                 Right Quit => Nothing

initDs : DataStore
initDs = MkData SString _ []

testDs : DataStore
testDs = MkData (SInt .+. SString) _ []

{- To execute in repl, idrs repl from src folder, :l this file and use :exec sec6_3b -}
export
covering
sec6_3b : IO ()
sec6_3b = replWith initDs "Command: " processInput
