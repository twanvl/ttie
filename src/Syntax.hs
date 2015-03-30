{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable #-}
{-# LANGUAGE ViewPatterns, PatternSynonyms #-}
{-# LANGUAGE TypeSynonymInstances, FlexibleInstances #-}
{-# LANGUAGE DataKinds #-}
module Syntax where

import Prelude ()
import Util.MyPrelude
import Util.Pretty
import Util.Parser
import Util.Tagged.Var
import qualified Util.Tagged.Internal as TV
import qualified Util.Tagged.Map as TM
import Substitution
import Names
import Tokenizer

import qualified Data.Map as Map
import qualified Data.Sequence as Seq
import Data.List (lookup,findIndex)
import Data.Default.Class

--------------------------------------------------------------------------------
-- Expressions
--------------------------------------------------------------------------------

-- Expressions and types
data Exp
  = Var  Int
  | Free Name
  | Binder Binder (Arg Exp) (Bound Exp)
  | App  Exp (Arg Exp)
  -- sets
  | Set  Level
  -- pairs
  | Proj Proj Exp
  | Pair Exp Exp Exp -- (x , y) : t
  -- equality
  -- | Eq   (Bound Exp) Exp Exp
  -- | Refl (Bound Exp)
  -- | Interval | I1 | I2 | I12 | I21
  -- | Fw Exp Exp | Bw Exp Exp | FwBw Exp Exp | BwFw Exp Exp | Adj Exp Exp | Equiv Exp Exp Exp Exp Exp
  -- typing
  | TypeSig Exp Exp
  | Meta MetaVar (Seq Exp)
  | Blank
  deriving (Eq)

-- Binders
data Binder = PiB | SiB | LamB
  deriving (Eq)

pattern Pi  x y = Binder PiB  x y
pattern Si  x y = Binder SiB  x y
pattern Lam x y = Binder LamB x y

type MetaVar = TaggedVar "meta"

-- | Fields in a pair
data Proj = Proj1 | Proj2
  deriving (Eq, Ord, Show, Enum)

-- Universe levels

-- Declarations
data Decl
  = DeclType
    { declNames :: [Name]
    , declType  :: Exp
    }
  | Rule
    { declLHS :: Exp
    , declRHS :: Exp
    }

{-
-- Data types
data DataType
  = DataType
    { dataArgs :: Telescoped a
data Telescoped a
  = TNil a
  | TCons (Arg Exp) (Bound Telescope)
-}

infixl 9 `App`, `AppV`, `AppH`
pattern AppV x y = App x (Arg Visible y)
pattern AppH x y = App x (Arg Hidden  y)

--------------------------------------------------------------------------------
-- Universe levels
--------------------------------------------------------------------------------

-- level is of the form  max x (maximum (?yi + zi))
-- invariant: x >= maximum zi
data Level = Level Int (TM.TaggedMap "level-meta" Int)
  deriving (Eq)

type LevelMetaVar = TaggedVar "level-meta"

intLevel :: Int -> Level
intLevel i = Level i TM.empty

zeroLevel :: Level
zeroLevel = intLevel 0

pattern IntLevel i <- Level i (TM.null -> True)
pattern ZeroLevel <- IntLevel 0

metaLevel :: LevelMetaVar -> Level
metaLevel mv = Level 0 $ TM.singleton mv 0

addLevel :: Int -> Level -> Level
addLevel x (Level i j) = Level (x + i) (map (x +) j)

sucLevel :: Level -> Level
sucLevel = addLevel 1

maxLevel :: Level -> Level -> Level
maxLevel (Level i j) (Level i' j') = Level (max i i') (TM.unionWith max j j')

--------------------------------------------------------------------------------
-- Constructors / combinators
--------------------------------------------------------------------------------

mkNat :: Int -> Exp
mkNat 0 = Free "zero"
mkNat n = Free "suc" `AppV` mkNat (n-1)

--------------------------------------------------------------------------------
-- Traversing expressions
--------------------------------------------------------------------------------

data ExpTraversal f = ExpTraversal
  { travVar  :: Int  -> f Exp
  , travFree :: Name -> f Exp
  }
defExpTraversal :: Applicative f => ExpTraversal f
defExpTraversal = ExpTraversal
  { travVar = \i -> pure $ Var i
  , travFree = \c -> pure $ Free c
  }

traverseExp :: Applicative f => Int -> ExpTraversal f -> (Exp -> f Exp)
traverseExp l f (Var i)
  | i < l     = pure $ Var i
  | otherwise = raiseBy l <$> travVar f (i - l)
traverseExp l f (Free c) = raiseBy l <$> travFree f c
traverseExp _ _ (Set i)  = pure $ Set i
traverseExp l f (Binder u a b) = Binder u <$> traverse (traverseExp l f) a <*> traverseBExp l f b
traverseExp l f (App a b) = App <$> traverseExp l f a <*> traverse (traverseExp l f) b
traverseExp l f (Proj a b) = Proj a <$> traverseExp l f b
traverseExp l f (Pair a b c) = Pair <$> traverseExp l f a <*> traverseExp l f b <*> traverseExp l f c
traverseExp l f (TypeSig a b) = TypeSig <$> traverseExp l f a <*> traverseExp l f b
traverseExp l f (Meta    a b) = Meta a <$> traverse (traverseExp l f) b
traverseExp _ _ Blank    = pure $ Blank
traverseBExp :: Applicative f => Int -> ExpTraversal f -> (Bound Exp -> f (Bound Exp))
traverseBExp l f = traverseBound (flip traverseExp f) l

foldExp :: Monoid m => Int -> (Int -> m) -> (Name -> m) -> (Exp -> m)
foldExp l0 f g = getConst . traverseExp l0 ExpTraversal
  { travVar = Const . f
  , travFree = Const . g }

instance Subst Exp where
  var = Var
  unVar (Var i) = Just i
  unVar _ = Nothing
  mapExpM f = traverseExp 0 defExpTraversal{ travVar = f }

--------------------------------------------------------------------------------
-- Renaming for printing and parsing
--------------------------------------------------------------------------------

-- free names
nameUsed :: Name -> Exp -> Bool
nameUsed v = getAny . foldExp 0 (\_ -> Any False) (\i -> Any $ i == v)

freshName :: Name -> Exp -> Name
freshName n x = head $ dropWhile (`nameUsed` x) (nameVariants n)

-- convert (Var i) to (Free _), for display
renameForPrinting :: Bound Exp -> Bound Exp
renameForPrinting (Bound n b)
  | varUsed 0 b = Bound n' (subst1 (Free n') b)
  | otherwise   = Bound "" b
  where
  n' = freshName n b

-- convert all unbound names to Vars
-- function specifies which Frees to keep

{-
-- precondition: the expression has no free variables
captureAll :: (Name -> Bool) -> Exp -> (Exp, Map.Map Name Int)
captureAll keep = flip runState Map.empty . traverseExp 0 ExpTraversal
  { travVar = \i -> error $ "captured: free variable " ++ show i
  , travFree = \n -> if keep n
    then return (Free n)
    else Var <$> lookupOrNew n
  }

lookupOrNew :: Ord a => a -> State (Map.Map a Int) Int
lookupOrNew x = state $ \s -> case Map.lookup x s of
  Just i  -> (i, s)
  Nothing -> (i, Map.insert x i s) where i = Map.size s
-}

-- convert a single given name to Var 0
capture :: Name -> Exp -> Bound Exp
capture n = Bound n . runIdentity . traverseExp 0 ExpTraversal
  { travVar = \i -> Identity $ Var (i + 1)
  , travFree = \n' -> Identity $ if n == n' then Var 0 else Free n'
  }

noCapture :: Exp -> Bound Exp
noCapture = Bound "" . raiseBy 1

{-
captureMany :: [Name] -> Exp -> Exp
captureMany ns = runIdentity . traverseExp 0 ExpTraversal
  { travVar = \i -> Identity $ Var (i + nn)
  , travFree = \c -> Identity $ case findIndex (c ==) ns of
     Just i  -> Var  i
     Nothing -> Free c
  }
  where nn = length ns
-}

--------------------------------------------------------------------------------
-- Pretty Printing
--------------------------------------------------------------------------------

{-
class PrettyM a where
  pprM :: TcEnv -> Int -> a -> Doc
-}

instance Pretty Exp where
  ppr _ (Var i) = text "#" <> ppr 0 i
  ppr p (Free c) = ppr p c
  ppr _ (Set ZeroLevel) = text "Set"
  ppr _ (Set (IntLevel i)) = text "Set" <> int i
  ppr _ (Set l) = text "Set" <> ppr 11 l
  ppr p (App a b) = group $ parenIf (p > 10) $ ppr 10 a $/$ ppr 11 b
  ppr p (Binder x a b) = case x of
    PiB  -> group $ parenIf (p > 1)  $ ppr 2 a' $/$ text "->" <+> ppr 1 b'
    SiB  -> group $ parenIf (p > 2)  $ ppr 3 a' $/$ text "*"  <+> ppr 2 b'
    LamB -> group $ parenIf (p > 1)  $ ppr 10 a' $/$ text "=>" <+> ppr 1 b'
    where (a',b') = namedBound a (renameForPrinting b)
  ppr p (Proj x y) = group $ parenIf (p > 10) $ text "proj" <> int (fromEnum x+1) <+> ppr 11 y
  ppr p (Pair x y _) = group $ parenIf (p > 2) $ align $ ppr 3 x <> text "," $$ ppr 2 y
  ppr p (TypeSig a b) = group $ parenIf (p > 0) $ ppr 1 a $/$ text ":" <+> ppr 0 b
  ppr _ (Meta i args)
    | Seq.null args = ppr 0 i
    | otherwise     = ppr 0 i <> semiBrackets (map (ppr 0) (toList args))
    -- | otherwise     = text "?" <> ppr 0 i <> semiBrackets [ ppr 0 a <+> text "=" <+> ppr 0 b | (a,b) <- IM.toList args]
  ppr _ Blank = text "_"

instance Pretty Level where
  ppr _ (IntLevel i) = int i
  ppr _ (Level l ls) = semiBrackets $ [int l|l>0] ++ [ ppr 0 mv <> if i == 0 then mempty else text "+" <> int i | (mv,i) <- TM.toList ls]

instance Pretty Decl where
  ppr p (DeclType names typ) = group $ parenIf (p > 0) $ hsep (map (ppr 0) names) $/$ text ":" <+> ppr 0 typ
  ppr p (Rule lhs rhs)       = group $ parenIf (p > 0) $ ppr 0 lhs $/$ text "=" <+> ppr 0 rhs

instance Pretty MetaVar where
  ppr _ (TV.TV i) = text "?" <> ppr 0 i
instance Pretty LevelMetaVar where
  ppr _ (TV.TV i) = text "?" <> ppr 0 i

instance Show Exp where
  showsPrec p = shows . ppr p
instance Show Level where
  showsPrec p = shows . ppr p
instance Show Decl where
  showsPrec p = shows . ppr p

--------------------------------------------------------------------------------
-- Parsing
--------------------------------------------------------------------------------

-- the parser needs to know which names are bound
type ParserEnv = (Name -> Bool)

parseExpPrim :: Int -> Parser Exp
parseExpPrim p
  =   tokLParen *> parseExp 0 <* tokRParen
  <|> mkBinders LamB <$ tokLambda <*> parseBinders <* (tokArrow <|> tokDot) <*> parseExp 0
  <|> mkBinders PiB  <$ tokForall <*> parseBinders <* (tokArrow <|> tokDot) <*> parseExp 0
  <|> mkBinders SiB  <$ tokExists <*> parseBinders <* (tokArrow <|> tokDot) <*> parseExp 0
  <|> Blank <$ tokUnderscore
  <|> Free <$> parseNonOpName
  <|> Set . intLevel <$> tokType
  <|> mkNat <$> tokInt
  <|> Var <$> tokVar
  <|> Meta . TV.TV <$> tokMeta <*> parseMetaArgs
  <|> Proj Proj1 <$ guard (p <= 10) <* tokReservedName "proj1" <*> parseExp 11
  <|> Proj Proj2 <$ guard (p <= 10) <* tokReservedName "proj2" <*> parseExp 11
  <?> "expression"

{-
parseMetaArgs :: Parser (IntMap Exp)
parseMetaArgs
  =   IM.fromList <$ tokLBracket <*> (parseMetaArg `sepBy` tokSemi) <* tokRBracket
  <|> return IM.empty
  where
  parseMetaArg :: Parser (Int,Exp)
  parseMetaArg = (,) <$> tokInt <* tokEquals <*> parseExp 0
-}
parseMetaArgs :: Parser (Seq Exp)
parseMetaArgs
  =   Seq.fromList <$ tokLBracket <*> (parseExp 0 `sepBy` tokSemi) <* tokRBracket
  <|> return Seq.empty 

parseExp :: Int -> Parser Exp
parseExp p = do
  lhs <- parseExpPrim p
  go 11 lhs
 <|> do
  -- "{x:a} -> b"
  x <- tokLBrace *> parseExp 0 <* tokRBrace
  (op,po,pr) <- parseBinderOp Hidden 11 p
  y <- parseExp pr
  go po =<< op x y
 where
  go pcur x
      = do (op,po,pr) <- parseOp pcur p
           y <- parseExp pr
           go po =<< op x y
    <|> return x


parseNonOpName :: Parser Name
parseNonOpName = (try $ do
  n <- tokName
  let opname = "_" ++ n ++ "_"
  case lookup opname infixNames of
    Just _ -> unexpected "operator"
    _ -> return n)
 <?> "name"
 
-- return (operator, precedence of lhs, precedence of result)
-- guard that precedence of result >= pmin
parseOp :: Int -> Int -> Parser (Exp -> Exp -> Parser Exp, Int, Int)
parseOp pcur pmin = (try $ do
  op <- tokName
  let opname = "_" ++ op ++ "_"
  case lookup opname infixNames of
    Just (po,pl,pr) | pcur >= pl && pmin <= po ->
         return (\x y -> pure $ Free opname `AppV` x `AppV` y,po,pr)
    _ -> unexpected $ "operator " ++ show op)
 <|> do
  guard $ pcur >= 1 && pmin <= 0
  tokColon
  return ((\x y -> pure (TypeSig x y)), 1,0)
 <|>
  parseBinderOp Visible pcur pmin
 <|> do
  guard $ pcur >= 10 && pmin <= 10
  return ((\x y -> pure (AppV x y)), 10, 11)

parseBinderOp :: Hiding -> Int -> Int -> Parser (Exp -> Exp -> Parser Exp, Int, Int)
parseBinderOp h pcur pmin = do
  guard $ pcur >= 2 && pmin <= 1
  tokArrow
  return (mkOpBinder PiB h, 2,1)
 <|> do
  guard $ pcur >= 3 && pmin <= 2
  tokProduct
  return (mkOpBinder SiB h, 3,2)
 <|> do
  guard $ pcur >= 4 && pmin <= 3
  tokThickArrow
  return (mkOpBinder LamB h, 4,3)

parseBinders :: Parser [NamedArg Exp]
parseBinders = concat <$> many parseBinder
parseBinder :: Parser [NamedArg Exp]
parseBinder
  =   map hidden  <$ tokLBrace <*> parsePrimBinder <* tokRBrace
  <|> map visible <$ tokLParen <*> parsePrimBinder <* tokRParen
  <|> (\n -> [visible (named n Blank)]) <$> tokName
  where
  parsePrimBinder :: Parser [Named Exp]
  parsePrimBinder =
     (\ns t -> map (flip named t) ns) <$> many1 tokName <*> (tokColon *> parseExp 1 <|> pure Blank)

-- Build a pi/sigma/lambda from operator notation.
-- note: this is not quite correct, since
--   (a b : foo a) -> c
-- is interpreted as
--   (a' : foo a) (b : foo a') -> c
-- so a is captured in the type of b
mkOpBinder :: Binder -> Hiding -> Exp -> Exp -> Parser Exp
mkOpBinder binder h (TypeSig a b) c = do
  ns <- toNames a
  return $ foldr (\n v -> Binder binder (Arg h b) (capture n v)) c ns
mkOpBinder binder h a c = return $ Binder binder (Arg h a) (noCapture c)

mkBinders :: Binder -> [NamedArg Exp] -> Exp -> Exp
mkBinders binder args c = foldr bind c args
  where
  bind :: NamedArg Exp -> Exp -> Exp
  bind (Arg h (Named n b)) v = Binder binder (Arg h b) (capture n v)

-- interpret an expression as a list of names
toNames :: Exp -> Parser [Name]
toNames (toName -> Just x) = return [x]
toNames (AppV xs (toName -> Just x)) = (++ [x]) <$> toNames xs
toNames x = failDoc $ text "Left hand side of ':' should be a list of names, found" $/$ ppr 0 x

toName :: Exp -> Maybe Name
toName (Free x) = Just x
toName _ = Nothing

{-
-- interpret an expression as a list of binders (x:a) (y:b)..
toBinders :: Exp -> Parser [Name]
toBinders (Free x)  = return [x]
toBinders (App xs (Free x)) = (++ [x]) <$> toNames xs
toBinders x = failDoc $ text "Left hand side of ':' should be a list of names, found" $/$ ppr 0 x
-}

parseDecl :: Parser Decl
parseDecl = do
  lhs <- parseExp 1
  id $ do tokColon
          names <- toNames lhs
          typ <- parseExp 0
          return $ DeclType names typ
   <|> do tokEquals
          rhs <- parseExp 0
          return $ Rule lhs rhs

parseDecls :: Parser [Decl]
parseDecls = withIndentation (many $ parseDecl0) <* tokWS <* eof
  where
  parseDecl0 = try (tokWS >> notIndented) >> withIndentation parseDecl

--------------------------------------------------------------------------------
-- Testing
--------------------------------------------------------------------------------

pe :: String -> Exp
pe = testParser (tokWS *> parseExp 0 <* eof)
pd :: String -> [Decl]
pd = testParser parseDecls
