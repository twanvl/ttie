module Util.Parser
  ( module Util.Parser
  , (<?>), P.many1, P.sepBy, P.try, P.eof, P.unexpected
  ) where

import Prelude ()
import Util.MyPrelude

import qualified Text.Parsec as P
import Text.Parsec ((<?>))

--------------------------------------------------------------------------------
-- Running parsers
--------------------------------------------------------------------------------

runParser :: Parser a -> FilePath -> String -> Either P.ParseError a
runParser p = P.runParser p Nothing

testParser :: Parser a -> String -> a
testParser p = fromRight . runParser p "input"

--------------------------------------------------------------------------------
-- Indentation handling
--------------------------------------------------------------------------------

-- | A parser that understands indentation
type Parser = P.Parsec String Indent
type Indent = Maybe P.SourcePos

noIndent :: Indent
noIndent = Nothing

-- succeed only if indentation is (>) reference, or token is on the same line
indented :: Parser ()
indented = do
  mr <- P.getState
  p <- P.getPosition
  case mr of
    Nothing -> return ()
    Just r
      | P.sourceColumn p > P.sourceColumn r
        || P.sourceLine p == P.sourceLine r -> return ()
    _ -> fail $ "indentation expected: " ++ show mr ++ " got " ++ show p

-- succeed only if indentation is (==) reference
notIndented :: Parser ()
notIndented = do
  mr <- P.getState
  p <- P.getPosition
  case mr of
    Just r
      | P.sourceColumn p == P.sourceColumn r -> return ()
    _ -> fail $ "no indentation expected: " ++ show mr ++ " got " ++ show p

localState :: st -> P.Parsec s st a -> P.Parsec s st a
localState stLocal p = do
  st <- P.getState
  P.putState stLocal
  a <- p
  P.putState st
  return a

-- set reference indentation level
withIndentation :: Parser a -> Parser a
withIndentation x = do
  p <- P.getPosition
  localState (Just p) x

withoutIndentation :: Parser a -> Parser a
withoutIndentation = localState noIndent

--------------------------------------------------------------------------------
-- Utility combinators
--------------------------------------------------------------------------------

-- parse left associative operator
parseChainL :: Parser (a -> b -> a) -> Parser a -> Parser b -> Parser a
parseChainL psep px py = px `optFollowedByMany` \x -> psep <*> pure x <*> py

parseChainL' :: (a -> Parser (b -> a)) -> Parser a -> Parser b -> Parser a
parseChainL' psep px py = px `optFollowedByMany` \x -> psep x <*> py

-- parse optional non-associative operator
parseChainN :: Parser (a -> b -> a) -> Parser a -> Parser b -> Parser a
parseChainN psep px py = px `optFollowedBy` \x -> psep <*> pure x <*> py

optFollowedBy :: Parser a -> (a -> Parser a) -> Parser a
optFollowedBy px py = px >>= (\x -> py x <|> return x)

optFollowedByMany :: Parser a -> (a -> Parser a) -> Parser a
optFollowedByMany px py = px >>= go
  where go x = (py x >>= go) <|> return x

