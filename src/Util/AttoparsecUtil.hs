
{- 
  Bunch of utility methods extending attoparsec.
  This mimics MiniParser I have implemented in Idris.
-}
module Util.AttoparsecUtil (
  optional
 , spaces
 , between
 , parseAll
) where
import Data.ByteString (ByteString)
import qualified Data.ByteString as B
import Data.ByteString.Char8 ()
import qualified Data.ByteString.Char8 as CH8
import Data.Attoparsec.ByteString hiding (takeTill)
import Data.Attoparsec.ByteString.Char8 

optional :: Parser a -> Parser (Maybe a)
optional p = option Nothing (Just <$> p)

spaces :: Parser [Char]
spaces = many1 space

between :: Parser a -> Parser b -> Parser ByteString
between from to = do
       fx <- from
       chars <- manyTill anyChar to
       return $ CH8.pack chars

parseAll :: Parser a -> ByteString -> Either String a
parseAll p str = parseOnly (p <* endOfInput) str
