module Part2.Sec6_3
import Data.Vect

%default total 

infixr 5 .+.

data Schema = SString
            | SInt
            | (.+.) Schema Schema

SchemaType : Schema -> Type
SchemaType SString = String
SchemaType SInt = Int
SchemaType (x .+. y) = (SchemaType x, SchemaType y)

{-
idris repl:
*src/Part2/Sec6_3> SchemaType (SInt .+. SString .+. SInt)
(Int, String, Int) : Type
-}     

{- This needs schema type parameter to cary the schema information around -}
data Command : Schema -> Type where
           -- works in context of old schema so this returns Command schema
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

getEntry : (pos : Integer) -> (store : DataStore) -> Maybe (String, DataStore)
getEntry pos store 
        = case integerToFin pos (size store) of
             Nothing => Just ("Out of range\n", store)
             Just id => Just (display (index id (items store)) ++ "\n", store)


setSchema : (store : DataStore) -> Schema -> Maybe DataStore
setSchema store schema = case size store of
       Z => Just (MkData schema _ [])
       S k => Nothing

parseSchema : List String -> Maybe Schema 
parseSchema ("String" :: xs)
     = case xs of
           [] => Just SString
           _ => do 
                  xs_sch <- parseSchema xs
                  Just (SString .+. xs_sch) 
parseSchema ("Int" :: xs)
     = case xs of
           [] => Just SInt
           _ => do 
                  xs_sch <- parseSchema xs
                  Just (SInt .+. xs_sch)
parseSchema _ = Nothing

||| That is the name the book is using, it is almost the same as parseBySchema but parses  
||| only part of the input string
parsePrefix : (schema : Schema) -> String -> Maybe (SchemaType schema, String) 
parsePrefix SString input = getQuoted (unpack input)
  where
     getQuoted : List Char -> Maybe (String, String) 
     getQuoted ('"' :: xs) = case span (/= '"') xs of
         (quoted, '"' :: rest) => Just (pack quoted, ltrim (pack rest)) 
         _ => Nothing
     getQuoted _ = Nothing
parsePrefix SInt input = case span isDigit input of 
              ("", rest) => Nothing
              (num, rest) => Just (cast num, ltrim rest)
parsePrefix (schemal .+. schemar) input = do
              (l_val, input') <- parsePrefix schemal input 
              (r_val, input'') <- parsePrefix schemar input' 
              Just ((l_val, r_val), input'')

||| same as parsePrefix only parses the whole input
parseBySchema : (schema : Schema) -> String -> Maybe (SchemaType schema) 
parseBySchema schema input = do
     (res, rest) <- parsePrefix schema input
     case rest of
        "" => Just res
        _ => Nothing

parseCommand : (schema : Schema) -> String -> String -> Maybe (Command schema) 
parseCommand schema "add" rest = do 
               restok <- parseBySchema schema rest
               Just (Add restok)
parseCommand schema "get" val = case all isDigit (unpack val) of
               False => Nothing
               True => Just (Get (cast val))
parseCommand schema "quit" "" = Just Quit
parseCommand schema "q" ""    = Just Quit
parseCommand schema "schema" rest = do 
               schemaok <- parseSchema (words rest)
               Just (SetSchema schemaok)
parseCommand _ _ _ = Nothing

parse : (schema : Schema) -> (input : String) -> Maybe (Command schema)
parse schema input = case span (/= ' ') input of
               (cmd, args) => parseCommand schema cmd (ltrim args)


processInput : DataStore -> String -> Maybe (String, DataStore)
processInput store input
          = case parse (schema store) input of
                 Nothing => Just ("Invalid command\n", store)
                 Just (Add item) =>
                    Just ("ID " ++ show (size store) ++ "\n", addToStore store item)
                 Just (Get pos) => getEntry pos store
                 Just (SetSchema schema') => case setSchema store schema' of
                        Nothing => Just ("Can't update schema\n", store)
                        Just store' => Just ("OK\n", store')
                 Just Quit => Nothing

export
partial
sec6_3 : IO ()
sec6_3 = replWith (MkData SString _ []) "Command: " processInput
