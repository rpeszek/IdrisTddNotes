||| Primitive monadic (non-transformer) parser
module Util.MiniParser
import Data.Vect

%default total
%access public export

data Parser a = P (String -> Either String (a, String))

parse :  Parser a -> String -> Either String (a, String)
parse (P f) str = f str

parseAll : Parser a -> String -> Either String a 
parseAll p str = do 
          (xa, rst) <- parse p str
          if rst == "" 
          then Right xa
          else Left ("did not parse " ++ rst)


onechar : Parser Char
onechar = P (\inp => case strM inp of
                    StrNil => Left "Error! Parsing empty list."
                    StrCons x xs => Right (x, xs))

interface Parsable a where
  item : Parser a

Parsable Char where
   item = onechar

interface Parsable a => Composite b a where
   compose : List a -> b

Composite String Char where
   compose = pack

Functor Parser where
  map f p = P (\inp => case parse p inp of
                          Left err        => Left err
                          Right (v, rest) => Right ((f v), rest))

Applicative Parser where
  pure v  = P (\inp => Right (v, inp))
  a <*> b = P (\inp => do (f, rest ) <- parse a inp
                          (x, rest') <- parse b rest
                          pure ((f x), rest'))

Monad Parser where
  p >>= f = P (\inp => case parse p inp of
                         Left err       => Left err
                         Right (v,rest) => parse (f v) rest)

||| choice of parsers
Alternative Parser where
  empty   = P (const (Left "empty"))
  p <|> q = P (\inp => case parse p inp of
                         Left msg      => parse q inp
                         Right (v,out) => Right (v,out))

fail : String -> Parser a
fail msg = P (\_ => Left msg)


infix 0 <?> 
||| similar to parsec allows to specify failure message
(<?>) : Parser a -> String -> Parser a
(<?>) p s = p <|> fail s

-- basic char parsers

accept : Parsable a => (a -> Bool) -> Parser a
accept f = do 
         x <- item
         if (f x) 
         then pure x 
         else empty


digit : Parser Char
digit = accept isDigit

lower : Parser Char
lower = accept isLower

upper : Parser Char
upper = accept isUpper

letter : Parser Char
letter = accept isAlpha

char : Char -> Parser Char
char c = accept (c ==)

charIngoreCase : Char -> Parser Char
charIngoreCase c = accept ((toUpper c) ==) <|> accept ((toLower c) ==)

string : String -> Parser String
string s = map pack (traverse char (unpack s))

stringIngoreCase : String -> Parser String
stringIngoreCase s = map pack (traverse charIngoreCase (unpack s))

-- combinators 

oneof : (Parsable a, Eq a) => List a -> Parser a
oneof xs = accept (\x => elem x xs)

optional : Parser a -> Parser (Maybe a)
optional p = map Just p <|> pure Nothing

notFollowedBy : Parser a -> Parser ()
notFollowedBy p = do 
          a <- optional p
          case a of
            Nothing => pure ()
            Just x => fail "not empty"

eof : Parser ()
eof = notFollowedBy onechar

||| apply p only if q is not applicable
unless :  Parser a -> Parser a -> Parser a
unless q p = P (\inp => case parse q inp of
                        (Left _)  => parse p inp
                        (Right _) => Left "unless failed"
               )

exactly :  (n : Nat) -> Parser a  -> Parser (Vect n a)
exactly Z _      = pure VNil
exactly (S n) p = [| p :: exactly n p |]

covering
many : Parsable a => Parser a -> Parser (List a)
many p = do
  (Just i) <- optional p
    | Nothing => pure VNil
  [| pure i :: many p |] 

covering
many1 : Parsable a => Parser a -> Parser (List a)
many1 p = do
    _ <- p
    many p

covering
spaces : Parser (List Char) 
spaces = many1 (char ' ')

covering
until : Parser a -> Parser a -> Parser (List a)
until to p = map reverse (untilrec to p VNil)
   where  
    partial
    untilrec : Parser a -> Parser a -> List a -> Parser (List a) 
    untilrec to p xa = do
               i <- optional to
               case i of 
                 Just _ => pure xa
                 Nothing => do
                   a <- p 
                   untilrec to p (a :: xa)


        
covering
between : (Parsable a, Composite b a) => Parser a -> Parser a -> Parser b 
between from to = do
        fx <- from
        as <- until to item
        pure (compose as)

covering
stringbetween : Parser Char -> Parser Char -> Parser String 
stringbetween = between

-- primitive parsers

covering
decimalInt : Parser Int
decimalInt = many digit >>= pure . cast . pack

covering
decimalInteger : Parser Integer
decimalInteger = many digit >>= pure . cast . pack
