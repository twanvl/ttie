module Tokenizer where

import Prelude ()
import Util.MyPrelude
import Util.Parser

import Data.Char
import qualified Text.Parsec as P

--------------------------------------------------------------------------------
-- Tokenizer
--------------------------------------------------------------------------------

data TokNameType = Reserved | User

-- primitive parts of the tokenizer

tokIntPart :: Parser Int
tokIntPart =
          P.char '0' *> zeroInt
      <|> parseBase 10 <$> P.many1 P.digit
      <?> "integer"
  where
  zeroInt = parseBase 16 <$ P.oneOf "xX" <*> P.many1 P.hexDigit
        <|> parseBase  8 <$ P.oneOf "oO" <*> P.many1 P.octDigit
        <|> parseBase  2 <$ P.oneOf "bB" <*> P.many1 (P.oneOf "01")
        <|> parseBase 10 <$> P.many P.digit
  parseBase :: Int -> String -> Int
  parseBase b = foldl' (\num x -> num * b + digitToInt x) 0

tokWS :: Parser ()
tokWS = P.skipMany (() <$ P.space <|> lineComment <|> nestedComment <?> "")
  where
  lineComment = P.try (P.string "--") *> lineCommentBody
  lineCommentBody = () <$ P.char '\n'
                <|> () <$ P.eof
                <|> P.anyChar *> lineCommentBody
  nestedComment = P.try (P.string "{-") *> nestedCommentBody
  nestedCommentBody = () <$ P.try (P.string "-}")
                  <|> nestedComment <* nestedCommentBody
                  <|> () <$ P.anyChar <* nestedCommentBody

-- tokens

tokNameEnd :: Parser ()
tokNameEnd = P.notFollowedBy $ P.satisfy isNameCont

tokIntEnd :: Parser ()
tokIntEnd = P.notFollowedBy $ P.satisfy isAlphaNum

tokAnyName :: Parser String
tokAnyName = (:) <$> P.satisfy isNameStart <*> P.many (P.satisfy isNameCont) <?> "name"

isNameStart, isNameCont :: Char -> Bool
--isNameStart x = isAlpha x || (isSymbol x) || x `elem` "_'*"
--isNameCont x = isAlphaNum x || (isSymbol x) || x `elem` "_'*"
isNameStart x = isAlpha x || (isSymbol x && x `notElem` "<=>^`$") || x `elem` "_'*"
isNameCont x = isAlphaNum x || (isSymbol x && x `notElem` "<=>^`") || x `elem` "_'*-"

-- a non-reserved name
tokName :: Parser String
tokName = P.try (do
  indented
  n <- tokAnyName
  when (isReservedName n) $ P.unexpected ("reserved name " ++ n)
  tokNameEnd
  tokWS
  return n
 <?> "name")

-- a path
tokPath :: Parser String
tokPath = P.try (do
  indented
  n <- tokString <|> P.many1 (P.satisfy (`notElem` " \t\n\r\""))
  tokWS
  return n
 <?> "path")

tokLowerName :: Parser String
tokLowerName = tokLowerNameNoWS <* tokWS <?> "name"

tokLowerNameNoWS :: Parser String
tokLowerNameNoWS = P.try (do
  indented
  n <- (:) <$> P.satisfy (\x -> isLower x || x `elem` "_") <*> P.many (P.satisfy isNameCont) <?> "name"
  tokNameEnd
  return n
 <?> "name")

tokUpperName :: Parser String
tokUpperName = P.try (do
  indented
  n <- (:) <$> P.satisfy isUpper <*> P.many (P.satisfy isNameCont) <?> "name"
  tokNameEnd
  tokWS
  return n
 <?> "name")

-- a non-reserved name
tokAQName :: Parser String
tokAQName = P.try (P.char '$' *> tokAnyName <* tokNameEnd) <* tokWS

isReservedName :: String -> Bool
isReservedName ('p':'r':'o':'j':(x:xs)) = all (`elem`"12") (x:xs)
isReservedName xs = xs `elem`
  ["Pi","Sigma","W","Top","Bot","Set","Type","Fin","Eq","refl","Interval","0","1","01","10"
  ,"cast","fw","bw","equiv"
  ,"forall","exists","proj1","proj2"
  ,"->",":",",","\\","\\/","=","of"
  ,"×","→","⇒","∀","Π","Σ","≡"]


tokReservedName :: String -> Parser ()
tokReservedName n = indented *> P.try (P.string n *> tokNameEnd) *> tokWS

tokReservedOp :: String -> Parser ()
tokReservedOp n = indented *> P.try (P.string n) *> tokWS

tokLParen, tokRParen, tokLBracket, tokRBracket, tokLBrace, tokRBrace, tokColon, tokSemi, tokComma, tokEquals, tokDEquals, tokArrow, tokThickArrow, tokProduct, tokHat, tokForall, tokExists, tokPi, tokSigma, tokLambda, tokBlank, tokCase, tokOf, tokEval, tokPostulate, tokDollar, tokDot, tokUnderscore, tokBacktick :: Parser ()
tokLParen = tokReservedOp "("
tokRParen = tokReservedOp ")"
tokLBracket = tokReservedOp "["
tokRBracket = tokReservedOp "]"
tokLBrace = tokReservedOp "{"
tokRBrace = tokReservedOp "}"
tokColon = tokReservedOp ":"
tokSemi = tokReservedOp ";"
tokComma = tokReservedOp ","
tokLambda = tokReservedOp "\\"
tokEquals = tokReservedOp "="
tokDEquals = tokReservedOp "=="
tokArrow = tokReservedOp "->" <|> tokReservedOp "→"
tokThickArrow = tokReservedOp "=>" <|> tokReservedOp "⇒"
tokProduct = tokReservedOp "*" <|> tokReservedOp "×"
tokHat = tokReservedOp "^"
tokForall = tokReservedName "forall" <|> tokReservedOp "\\/" <|> tokReservedOp "∀"
tokExists = tokReservedName "exists" <|> tokReservedOp "∃"
tokPi = tokReservedName "Pi" <|> tokReservedOp "Π"
tokSigma = tokReservedName "Sigma" <|> tokReservedOp "Σ"
tokBlank = tokReservedName "_"
tokCase = tokReservedName "case"
tokOf = tokReservedName "of"
tokEval = tokReservedName "eval"
tokPostulate = tokReservedName "postulate"
tokDollar = tokReservedOp "$"
tokDot = tokReservedOp "."
tokUnderscore = tokReservedName "_"
tokBacktick = tokReservedOp "`"

tokType :: Parser Int
tokType = indented *> P.try ((P.string "Type" <|> P.string "Set") *> (tokIntPart <|> return 0) <* tokNameEnd) <* tokWS

tokEq :: Parser String
tokEq = indented *> P.try (P.string "Eq" *> (tokNameEnd *> return "" <|> P.string "_" *> tokAnyName)) <* tokWS

tokRefl :: Parser String
tokRefl = indented *> P.try (P.string "refl" *> (tokNameEnd *> return "" <|> P.string "_" *> tokAnyName)) <* tokWS

tokCast :: Parser String
tokCast = indented *> P.try (P.string "cast" *> (tokNameEnd *> return "" <|> P.string "_" *> tokAnyName)) <* tokWS

tokFw :: Parser String
tokFw = indented *> P.try (P.string "fw" *> (tokNameEnd *> return "" <|> P.string "_" *> tokAnyName)) <* tokWS

tokBw :: Parser String
tokBw = indented *> P.try (P.string "bw" *> (tokNameEnd *> return "" <|> P.string "_" *> tokAnyName)) <* tokWS

tokFin :: Parser Int
tokFin = indented *> P.try (P.string "Fin" *> tokIntPart <* tokNameEnd) <* tokWS
     <|> 0 <$ (tokReservedName "⊥" <|> tokReservedName "Bot")
     <|> 1 <$ (tokReservedName "⊤" <|> tokReservedName "Top")
     <|> 2 <$ (tokReservedName "Bool")

tokProj :: Parser [Int]
tokProj = P.try (tokReservedOp "proj" *> P.many1 (pred . read . return <$> P.oneOf "12") <* tokNameEnd) <* tokWS

tokInj :: Parser (Int,Maybe Int)
tokInj = indented *> P.try (do
  _ <- tokReservedOp "inj"
  i <- tokIntPart
  tokNameEnd
  return (i,Nothing)) <* tokWS
 <|> (0,Just 1) <$ tokReservedName "tt"
 <|> (0,Just 2) <$ tokReservedName "true"
 <|> (1,Just 2) <$ tokReservedName "false"

tokInt :: Parser Int
tokInt = tokIntPart <* tokIntEnd <* tokWS <?> "number"

tokVar :: Parser Int
tokVar = indented *> P.try (P.string "#" *> tokIntPart <* tokIntEnd) <* tokWS
  <?> "de Bruijn variable"

tokMeta :: Parser Int
tokMeta = indented *> P.try (P.string "?" *> tokIntPart <* tokIntEnd) <* tokWS
  <?> "meta variable"

tokString :: Parser String
tokString = indented *> P.try (P.char '"' *> P.many stringPart <* P.char '"') <* tokWS
  where
  stringPart = P.satisfy (`notElem` "\"\\\n")
           <|> '\\' <$ P.string "\\\\"
           <|> '\"' <$ P.string "\\\""
           <|> '\n' <$ P.string "\\n"
           <|> '\r' <$ P.string "\\r"

