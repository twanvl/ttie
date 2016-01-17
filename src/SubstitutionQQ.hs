{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable #-}
{-# LANGUAGE ViewPatterns, PatternSynonyms, PatternGuards #-}
{-# LANGUAGE DataKinds, KindSignatures #-}
{-# LANGUAGE TemplateHaskell #-}
module SubstitutionQQ
  (Wrap(..),qq)
  where

import Prelude ()
import Util.MyPrelude
import Util.Parser
import Tokenizer
import Substitution

import Data.Data (Data)
import Data.List (findIndex)

import qualified Text.Parsec as P
import qualified Text.Parsec.Pos as P

import GHC.TypeLits

import Language.Haskell.TH as TH
import Language.Haskell.TH.Quote as TH

--------------------------------------------------------------------------------
-- Template haskell to improve safety
--------------------------------------------------------------------------------

-- The idea is that you write [qq| Foo ([x] Bar y) |]
-- to indicate that the variable "x" is bound inside (Bar y)
-- the only way to get back to a normal expression is by [qq| Baz (x: y)] or [qq| y[x=..] ].
-- raising/substitution is then performed automatically.

-- Desugaring:
--   Foo ([x](Bar [y]z)) = Foo (Bar [x][y]z)
--   [x1]..[xn] xi = var (n-i)
--   [x1]..[xn] z  = z[x1,...,xn] = z[x1=x1,...,xn=xn]
--   [x1]..[xn] z[y1=u1,yn=un] = raiseSubst n (reverse [u1,..,un])

-- More sugar:
--   [$x] y = Bound $x [x]y
--   [~x] y = wrap "x" [x]y
--   [%x:t] y = sequenceBound t (Bound $x [x]y)
--   %x y z = x y z
--   x `F` y     =  F x y
-- More sugar (TODO):
--   (x:a) -> b  =  Pi  a [x]b
--   (x:a) *  b  =  Si  a [x]b
--   (x:a) => b  =  Lam a [x]b

--------------------------------------------------------------------------------
-- Syntax and parsing
--------------------------------------------------------------------------------

-- possible patterns
type ConName = Name
type VarName = String
type BoundName = String
data GenBind 
  = Con  ConName [GenBind]
  | Fun  ExpQ    [GenBind]
  | Var  [BoundName] Bool VarName (Maybe [(BoundName,GenBind)])
  deriving ()

bind :: BoundName -> GenBind -> GenBind
bind b (Con x xs) = Con x (map (bind b) xs)
bind b (Fun x xs) = Fun x (map (bind b) xs)
bind b (Var bs True  x xs) = Var (b:bs) True  x (fmap (map (second (bind b))) xs)
bind b (Var bs False x xs) = Var bs     False x (fmap (map (second (bind b))) xs)

bindBound :: BoundName -> GenBind -> GenBind
bindBound n x = Con (mkName "Bound") [Var [] False n Nothing, bind n x]
bindSequence :: BoundName -> GenBind -> GenBind -> GenBind
bindSequence n t x = Fun (varE $ mkName "sequenceBound") [t,bindBound n x]
bindWrap :: BoundName -> GenBind -> GenBind
bindWrap n x = Fun (wrapQ n) [bind n x]

isBoundVar :: GenBind -> Maybe Int
isBoundVar (Var bs _ x Nothing) = findIndex (==x) (reverse bs)
isBoundVar _ = Nothing
pattern BoundVar i <- (isBoundVar -> Just i)

--------------------------------------------------------------------------------
-- Parsing
--------------------------------------------------------------------------------

parseGenBind :: Int -> Parser GenBind
parseGenBind p = do
  x <- parseGenBindSimple p
  go x
  where
  go x = (do
      guard (p < 10)
      n <- tokBacktick *> tokUpperName <* tokBacktick
      y <- parseGenBindSimple 10
      go (Con (mkName n) [x,y])
    ) <|> return x

parseGenBindSimple :: Int -> Parser GenBind
parseGenBindSimple p
  =   tokLParen *> parseGenBind 0 <* tokRParen
  <|> (Con . mkName) <$> tokUpperName <*>
      (guard (p <= 10) *> many (parseGenBind 11) <|> return [])
  <|> (Fun . varE . mkName) <$ tokReservedOp "%" <*> tokName <*>
      (guard (p <= 10) *> many (parseGenBind 11) <|> return [])
  <|> tokLBracket *> (bindBound <$ tokDollar <*> tokLowerName
                  <|> bindWrap <$ tokReservedOp "~" <*> tokLowerName
                  <|> bindSequence <$ tokReservedOp "%" <*> tokLowerName <* tokColon <*> parseGenBindSimple 0
                  <|> bind <$> tokLowerName)
                  <* tokRBracket <*> parseGenBind p
  <|> Var [] <$> (False <$ tokDollar <|> pure True)
             <*> tokLowerNameNoWS <*>
      (Just <$ tokLBracket <*> (P.sepBy parseSubst tokComma) <* tokRBracket <|>
       Nothing <$ tokWS)

parseSubst :: Parser (BoundName,GenBind)
parseSubst = do
  n <- tokLowerName
  v <- tokEquals *> parseGenBind 0 <|> return (Var [] True n Nothing)
  return (n,v)

--------------------------------------------------------------------------------
-- Template Haskell: utility
--------------------------------------------------------------------------------

posFromTH :: TH.Loc -> P.SourcePos
posFromTH loc = P.newPos (TH.loc_filename loc) (fst (TH.loc_start loc)) (snd (TH.loc_start loc))

-- run a parser with correct localitions
parseTH :: Parser a -> String -> TH.Q a
parseTH p s = do
  loc <- TH.location
  case P.runParser (P.setPosition (posFromTH loc) *> p <* P.eof) Nothing "" s of
    Left err  -> fail $ show err ++ " in quasi quote"
    Right e   -> return e

dataP :: Data a => a -> PatQ
dataP = dataToPatQ (\_ -> Nothing)

dataE :: Data a => a -> ExpQ
dataE = dataToExpQ (\_ -> Nothing)

--------------------------------------------------------------------------------
-- Support functions/types
--------------------------------------------------------------------------------

newtype Wrap (s :: Symbol) x = Wrap { unwrap :: x }
  deriving (Functor,Foldable,Traversable)

--------------------------------------------------------------------------------
-- Template haskell
--------------------------------------------------------------------------------

wrapQ :: String -> ExpQ
wrapQ n = do
  -- [e|Wrap :: a -> Wrap "b" a|]
  wrapE <- [e|Wrap|]
  wrapT <- [t|Wrap|]
  a <- newName "a"
  let wrap_na = wrapT `AppT` LitT (StrTyLit n) `AppT` VarT a
  parensE $ return $ SigE wrapE (ForallT [PlainTV a] [] (ArrowT `AppT` VarT a `AppT` wrap_na))

unwrapQ :: String -> ExpQ
unwrapQ n = do
  -- [e|unwrap :: Wrap "b" a -> a|]
  unwrapE <- [e|unwrap|]
  wrapT <- [t|Wrap|]
  a <- newName "a"
  let wrap_na = wrapT `AppT` LitT (StrTyLit n) `AppT` VarT a
  parensE $ return $ SigE unwrapE (ForallT [PlainTV a] [] (ArrowT `AppT` wrap_na `AppT` VarT a))

mkSubst' :: Int -> [ExpQ] -> ExpQ -> ExpQ
mkSubst' 0 [] x = x
mkSubst' n [] x = [| raiseBy |] `appE` dataE n `appE` x
mkSubst' n xs x = [| raiseSubsts |] `appE` dataE n `appE` (listE xs) `appE` x

mkSubst :: Int -> [ExpQ] -> ExpQ -> ExpQ
mkSubst n xs y
  | n > 0 && length xs > 0 = do
     -- simplify the substitution: raiseSubst (n+1) [x1,x2,..,x{i-1},var n] = raiseSubst n [x1,x2,..,x{i-1}]
     -- testing whether last xs == var i requires that we evaluate the ExpQs to Exps
     lx  <- last xs
     lx' <- appE [e|var|] (dataE (n - 1))
     if lx == lx'
      then mkSubst (n-1) (init xs) y
      else mkSubst' n xs y
  | otherwise = mkSubst' n xs y

mkUnsubst :: [Maybe Int] -> PatQ -> PatQ
mkUnsubst [] = id
mkUnsubst xs
  | last xs == Just (length xs - 1) = mkUnsubst (init xs)
  | all isNothing xs = viewP ([| lowerBy |] `appE` dataE (length xs)) . justP
  | otherwise        = viewP ([| raiseSubstsM |] `appE` dataE (length $ filter isJust xs) `appE` listE xs') . justP
  where
  xs' = map (maybe [|Nothing|] (\x -> [|Just|] `appE` ([|var|] `appE` dataE x))) xs

justP :: PatQ -> PatQ
justP x = conP 'Just [x] --'

toPat :: GenBind -> PatQ
toPat (Con x xs) = conP x (map toPat xs)
toPat (Fun _ _) = error "Functions not supported in patterns"
toPat (BoundVar i) = viewP [e|unVar|] (dataP (Just i))
--toPat (Var bs _ x Nothing) = foldr (\b -> viewP (wrapQ b)) (varP (mkName x)) bs
--toPat (Var bs _ x (Just [])) = error $ "Lower by " ++ show (length bs)
--toPat (Var _  _ _ (Just _)) = error "Can't handle substitution in patterns"
toPat (Var bs _ x ss)
  | any (`notElem` bs) ss' = error $ "Unknown variables: " ++ show (filter (`notElem` bs) ss')
  | otherwise = unsubst
  where
  ss' = maybe bs (map fst) ss -- names to wrap in
  -- mapping back
  namePat | x == "_"  = wildP
          | otherwise = varP (mkName x)
  wrapped = foldr (\b -> viewP (wrapQ b)) namePat (reverse ss')
  unsubst = mkUnsubst [findIndex (b==) (reverse ss') | b <- reverse bs] wrapped

toExp :: GenBind -> ExpQ
toExp (Con x xs) = foldl appE (conE x) (map toExp xs)
toExp (Fun x xs) = foldl appE x        (map toExp xs)
toExp (BoundVar i) = appE [e|var|] (dataE i)
toExp (Var bs bb x ss) = mkSubst (length bs) (map (toExp . snd) (reverse ss')) (unwrapped)
  where
  -- if there is no substitution, then assume that all bound variables are to be substituted
  ss' = fromMaybe (map (\n -> (n,Var bs bb n Nothing)) bs) ss
  unwrapped = foldr (\(b,_) -> appE (unwrapQ b)) (varE (mkName x)) (reverse ss')

qq :: QuasiQuoter
qq = QuasiQuoter
  { quoteExp = toExp <=< parseTH (tokWS *> parseGenBind 0 <* P.eof)
  , quotePat = toPat <=< parseTH (tokWS *> parseGenBind 0 <* P.eof)
  , quoteType = fail "exp is not a Type quasi quoter"
  , quoteDec  = fail "exp is not a Declaration quasi quoter"
  }


