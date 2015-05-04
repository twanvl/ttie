{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable #-}
{-# LANGUAGE ViewPatterns, PatternSynonyms #-}
{-# LANGUAGE TypeSynonymInstances, FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
module Syntax where

import Prelude ()
import Util.MyPrelude
import Util.PrettyM
import Util.Parser
import Util.Tagged.Var
import qualified Util.Tagged.Internal as TV
import qualified Util.Tagged.Map as TM
import Substitution
import Names
import Tokenizer

import qualified Data.Map as Map
import qualified Data.Set as Set
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
  | Proj (Arg Proj) Exp
  | Pair (Arg Exp) Exp Exp -- (x , y) : t
  -- unit type
  | UnitTy
  | UnitVal
  -- sum types
  | SumTy [SumCtor]
  | SumVal Name Exp Exp
  | SumElim Exp [SumCase] Exp -- case x of {..} : (..) x
  -- equality
  | Eq   (Bound Exp) Exp Exp
  | Refl (Bound Exp)
  | Cast (Bound Exp) Exp Exp Exp
  | Equiv Exp Exp Exp Exp Exp
  -- interval
  | Interval | I1 | I2 | I12 | I21 | IFlip Exp
  | IV Exp Exp Exp Exp
  -- typing
  | TypeSig Exp Exp
  | Meta MetaVar (Seq Exp)
  | Blank
  deriving (Eq)

-- Binders
data Binder = PiB | SiB | LamB
  deriving (Eq)

type MetaVar = TaggedVar "meta"

-- | Fields in a pair
data Proj = Proj1 | Proj2
  deriving (Eq, Ord, Show, Enum)

-- | Sum constructors and cases
data SumCtor = SumCtor { ctorName :: Name, ctorType :: Exp } -- n : a
  deriving (Eq)
data SumCase = SumCase { caseName :: Name, caseType :: Exp, caseBody :: Bound Exp } -- n (x:a) -> b
  deriving (Eq)

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

pattern Pi  x y = Binder PiB  x y
pattern Si  x y = Binder SiB  x y
pattern Lam x y = Binder LamB x y

infixl 9 `App`, `AppV`, `AppH`
pattern AppV x y = App x (Arg Visible y)
pattern AppH x y = App x (Arg Hidden  y)

pattern PiV x y = Pi (Arg Visible x) y
pattern PiH x y = Pi (Arg Hidden  x) y

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

metaLevel :: LevelMetaVar -> Level
metaLevel mv = Level 0 $ TM.singleton mv 0

pattern IntLevel i <- Level i (TM.null -> True)
pattern ZeroLevel <- IntLevel 0
pattern MetaLevel mv <- Level 0 (TM.toList -> [(mv,0)])

addLevel :: Int -> Level -> Level
addLevel x (Level i j) = Level (x + i) (map (x +) j)

subtractLevel :: Int -> Level -> Maybe Level
subtractLevel x (Level i j) = Level <$> trySubtract x i <*> traverse (trySubtract x) j

sucLevel :: Level -> Level
sucLevel = addLevel 1

maxLevel :: Level -> Level -> Level
maxLevel (Level i j) (Level i' j') = Level (max i i') (TM.unionWith max j j')

maxLevels :: [Level] -> Level
maxLevels = foldr maxLevel zeroLevel

--------------------------------------------------------------------------------
-- Constructors / combinators
--------------------------------------------------------------------------------

mkNat :: Int -> Exp
mkNat 0 = Free "zero"
mkNat n = Free "suc" `AppV` mkNat (n-1)

caseToCtor :: SumCase -> SumCtor
caseToCtor (SumCase n u _) = SumCtor n u

--------------------------------------------------------------------------------
-- Traversing expressions
--------------------------------------------------------------------------------

instance TraverseChildren Exp Exp where
  traverseChildren _ (Var i)  = pure $ Var i
  traverseChildren _ (Free c) = pure $ Free c
  traverseChildren _ (Set i)  = pure $ Set i
  traverseChildren f (Binder u (Arg h x) y) = traverseBinder (Binder u . Arg h) f f x y
  traverseChildren f (App x y) = App <$> f x <*> traverse f y
  traverseChildren f (Proj x y) = Proj x <$> f y
  traverseChildren f (Pair x y z) = Pair <$> traverse f x <*> f y <*> f z
  traverseChildren _ UnitTy = pure UnitTy
  traverseChildren _ UnitVal = pure UnitVal
  traverseChildren f (SumTy xs) = SumTy <$> traverse (traverseChildren f) xs
  traverseChildren f (SumVal x y z) = SumVal x <$> f y <*> f z
  traverseChildren f (SumElim x ys z) = SumElim <$> f x <*> traverse (traverseChildren f) ys <*> f z
  traverseChildren f (Eq x y z) = Eq <$> traverseBound Interval f x <*> f y <*> f z
  traverseChildren f (Refl x) = Refl <$> traverseBound Interval f x
  traverseChildren _ Interval = pure Interval
  traverseChildren _ I1 = pure I1
  traverseChildren _ I2 = pure I2
  traverseChildren _ I12 = pure I12
  traverseChildren _ I21 = pure I21
  traverseChildren f (IFlip x) = IFlip <$> f x
  traverseChildren f (IV x y z w) = IV <$> f x <*> f y <*> f z <*> f w
  traverseChildren f (Cast  a b c d) = Cast <$> traverseBound Interval f a <*> f b <*> f c <*> f d
  traverseChildren f (Equiv a b c d e) = Equiv <$> f a <*> f b <*> f c <*> f d <*> f e
  traverseChildren f (TypeSig x y) = TypeSig <$> f x <*> f y
  traverseChildren f (Meta    x y) = Meta x <$> traverse f y
  traverseChildren _ Blank    = pure $ Blank

instance TraverseChildren Exp SumCtor where
  traverseChildren f (SumCtor n x) = SumCtor n <$> f x
instance TraverseChildren Exp SumCase where
  traverseChildren f (SumCase n x y) = traverseBinder (SumCase n) f f x y

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
traverseExp l f x = runDepthT l $ traverseChildren (\x' -> withDepth $ \l' -> traverseExp l' f x') x

foldExp :: Monoid m => Int -> (Int -> m) -> (Name -> m) -> (Exp -> m)
foldExp l0 f g = getConst . traverseExp l0 ExpTraversal
  { travVar = Const . f
  , travFree = Const . g }

instance Subst Exp where
  var = Var
  unVar (Var i) = Just i
  unVar _ = Nothing

--------------------------------------------------------------------------------
-- Renaming for printing and parsing
--------------------------------------------------------------------------------

-- free names
nameUsed :: Name -> Exp -> Bool
nameUsed v = getAny . foldExp 0 (\_ -> Any False) (\i -> Any $ i == v)

freeNames :: Exp -> Set Name
freeNames = foldExp 0 (\_ -> Set.empty) Set.singleton

freshName :: Name -> Exp -> Name
freshName n x = head $ dropWhile (`nameUsed` x) (nameVariants n)

-- convert (Var i) to (Free _), for display
renameForPrinting :: Bound Exp -> Bound Exp
renameForPrinting (Bound n b)
  | varUsed 0 b = Bound n' (subst1 (Free n') b)
  | otherwise   = Bound "" b
  where
  n' = freshName n b

nameForPrinting :: Bound Exp -> Bound Exp
nameForPrinting (Bound n b)
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

instance (MonadBound Exp m, MonadBoundNames m) => Pretty m Exp where
  --ppr _ (Var i) = text "#" <.> ppr 0 i
  ppr _ (Var i) = do
    mname <- seqLookup i <$> boundNames
    case mname of
      Just n  -> text n <.> text "#" <.> ppr 0 i
      Nothing -> text "#" <.> ppr 0 i
  ppr p (Free c) = ppr p c
  ppr _ (Set ZeroLevel) = text "Set"
  ppr _ (Set (IntLevel i)) = text "Set" <.> int i
  ppr _ (Set l) = text "Set" <.> ppr 11 l
  ppr p (App a b) = group $ parenAlignIf (p > 10) $ ppr 10 a $/$ ppr 11 b
  {-ppr p (Binder x a b) = do
    where (a',b') = namedBound a (renameForPrinting b)
    case x of
      PiB  -> group $ parenIf (p > 1) $ ppr 2 a' $/$ text "->" <+> localBound (argValue a') (ppr 1 b')
      SiB  -> group $ parenIf (p > 2) $ ppr 3 a' $/$ text "*"  <+> localBound (argValue a') (ppr 2 b')
      LamB -> group $ parenIf (p > 1) $ ppr 10 a' $/$ text "=>" <+> localBound (argValue a') (ppr 1 b')-}
  ppr p (Binder x a b) = case x of
    PiB  -> group $ parenAlignIf (p > 1) $ ppr 2 a' $/$ text "->" <+> localBound (argValue a') (ppr 1 b')
    SiB  -> group $ parenAlignIf (p > 2) $ ppr 3 a' $/$ text "*"  <+> localBound (argValue a') (ppr 2 b')
    LamB -> group $ parenAlignIf (p > 1) $ ppr 10 a' $/$ text "=>" <+> localBound (argValue a') (ppr 1 b')
    where (a',b') = namedBound a (renameForPrinting b)
  ppr _ (UnitTy)  = text "Unit"
  ppr _ (UnitVal) = text "tt"
  ppr _ (SumTy xs) = group $ text "data" <+> semiBraces (map (ppr 0) xs)
  ppr p (SumVal x y _) = group $ parenAlignIf (p > 10) $ text "value" <+> text x <+> ppr 11 y
  ppr _ (SumElim x ys _) = group $ text "case" <+> ppr 0 x <+> text "of" <+> semiBraces (map (ppr 0) ys)
  ppr p (Proj x y) = group $ parenIf (p > 10) $ ppr p x <+> ppr 11 y
  ppr p (Pair x y _) = group $ parenIf (p > 2) $ align $ ppr 3 x <.> text "," $$ ppr 2 y
  ppr p (Eq x y z) = group $ parenAlignIf (p > 10) $ case renameForPrinting x of
    Bound "" x' -> text "Eq"             <+> ppr 11 x' <+> ppr 11 y <+> ppr 11 z
    Bound n x'  -> text "Eq_" <.> text n <+> ppr 11 x' <+> ppr 11 y <+> ppr 11 z
  ppr p (Refl x) = group $ parenAlignIf (p > 10) $ case renameForPrinting x of
    Bound "" x' -> text "refl"             <+> ppr 11 x'
    Bound n x'  -> text "refl_" <.> text n <+> ppr 11 x'
  ppr _ Interval = text "Interval"
  ppr _ I1 = text "i1"
  ppr _ I2 = text "i2"
  ppr _ I12 = text "i12"
  ppr _ I21 = text "i21"
  ppr p (IFlip x) = group $ parenIf (p > 10) $ text "iflip" <+> ppr 11 x
  --ppr p (IV _x _y z w) = group $ parenIf (p > 11) $ ppr 11 z <.> text "^" <.> ppr 12 w
  ppr p (IV x y z w) = group $ parenAlignIf (p > 10) $ text "iv" <+> ppr 11 x <+> ppr 11 y <+> ppr 11 z <+> ppr 11 w
  ppr p (Cast  a b c d) = group $ parenAlignIf (p > 10) $ case renameForPrinting a of
    Bound "" a' -> text "cast"             <+> ppr 11 a' <+> ppr 11 b <+> ppr 11 c <+> ppr 11 d
    Bound n  a' -> text "cast_" <.> text n <+> ppr 11 a' <+> ppr 11 b <+> ppr 11 c <+> ppr 11 d
  ppr p (Equiv a b c d e) = group $ parenIf (p > 10) $ text "equiv" <+> ppr 11 a <+> ppr 11 b <+> ppr 11 c <+> ppr 11 d <+> ppr 11 e
  ppr p (TypeSig a b) = group $ parenIf (p > 0) $ ppr 1 a $/$ text ":" <+> ppr 0 b
  ppr _ (Meta i args)
    | Seq.null args = ppr 0 i
    | otherwise     = ppr 0 i <.> semiBrackets (map (ppr 0) (toList args))
  ppr _ Blank = text "_"

instance Applicative m => Pretty m Proj where
  ppr _ Proj1 = text "proj1"
  ppr _ Proj2 = text "proj2"

instance (MonadBound Exp m, MonadBoundNames m) => Pretty m SumCtor where
  ppr _ (SumCtor n x) = text n <+> text ":" <+> ppr 0 x

instance (MonadBound Exp m, MonadBoundNames m) => Pretty m SumCase where
  ppr _ (SumCase n x y) = text n <+> ppr 1 (Named yN x) <+> text "->" <+> ppr 0 (boundBody y')
    where
    y' = renameForPrinting y
    yN = if boundName y' == "" then "_" else boundName y'

instance Applicative m => Pretty m Level where
  ppr _ (IntLevel i) = int i
  ppr _ (Level l ls) = semiBrackets $ [int l|l>0] ++ [ ppr 0 mv <.> if i == 0 then emptyDoc else text "+" <.> int i | (mv,i) <- TM.toList ls]

instance (MonadBound Exp m, MonadBoundNames m) => Pretty m Decl where
  ppr p (DeclType names typ) = group $ parenIf (p > 0) $ hsep (map (ppr 0) names) $/$ text ":" <+> ppr 0 typ
  ppr p (Rule lhs rhs)       = group $ parenIf (p > 0) $ ppr 0 lhs $/$ text "=" <+> ppr 0 rhs

instance Applicative m => Pretty m MetaVar where
  ppr _ (TV.TV i) = text "?" <.> ppr 0 i
instance Applicative m => Pretty m LevelMetaVar where
  ppr _ (TV.TV i) = text "?l" <.> ppr 0 i

instance Show Exp where
  showsPrec p = showsDoc . runIdentity . runNamesT . ppr p
instance Show SumCtor where
  showsPrec p = showsDoc . runIdentity . runNamesT . ppr p
instance Show SumCase where
  showsPrec p = showsDoc . runIdentity . runNamesT . ppr p
instance Show Level where
  showsPrec p = showsDoc . runIdentity . runNamesT . ppr p
instance Show Decl where
  showsPrec p = showsDoc . runIdentity . runNamesT . ppr p

showExp :: NamesT Identity Doc -> String
showExp = showDoc . runIdentity . runNamesT

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
  <|> Set . intLevel <$> tokType
  <|> mkNat <$> tokInt
  <|> Var <$> tokVar
  <|> Proj (visible Proj1) <$ guard (p <= 10) <* tokReservedName "proj1" <*> parseExp 11
  <|> Proj (visible Proj2) <$ guard (p <= 10) <* tokReservedName "proj2" <*> parseExp 11
  <|> Proj (hidden  Proj1) <$ guard (p <= 10) <* try (tokLBrace *> tokReservedName "proj1" <* tokRBrace) <*> parseExp 11
  <|> Proj (hidden  Proj2) <$ guard (p <= 10) <* try (tokLBrace *> tokReservedName "proj2" <* tokRBrace) <*> parseExp 11
  <|> UnitTy <$ tokReservedName "Unit"
  <|> UnitVal <$ tokReservedName "tt"
  <|> SumTy   <$ tokReservedName "data" <* tokLBrace <*> parseSumCtor `sepBy` tokSemi <* tokRBrace
  <|> SumElim <$ tokReservedName "case" <*> parseExp 11 <* tokReservedName "of" <* tokLBrace <*> parseSumCase `sepBy` tokSemi <* tokRBrace <*> pure Blank
  <|> SumVal <$ tokReservedName "value" <*> tokName <*> parseExp 11 <*> pure Blank
  <|> Interval <$ tokReservedName "Interval"
  <|> I1 <$ tokReservedName "i1"
  <|> I2 <$ tokReservedName "i2"
  <|> I12 <$ tokReservedName "i12"
  <|> I21 <$ tokReservedName "i21"
  <|> IFlip <$ guard (p <= 10) <* tokReservedName "iflip" <*> parseExp 11
  <|> IV <$ guard (p <= 10) <* tokReservedName "iv" <*> parseExp 11 <*> parseExp 11 <*> parseExp 11 <*> parseExp 11
  <|> (\n x -> Refl (capture n x)) <$ guard (p <= 10) <*> tokRefl <*> parseExp 11
  <|> (\n x -> Eq   (capture n x)) <$ guard (p <= 10) <*> tokEq   <*> parseExp 11 <*> parseExp 11 <*> parseExp 11
  <|> (\n x -> Cast (capture n x)) <$ guard (p <= 10) <*> tokCast <*> parseExp 11 <*> parseExp 11 <*> parseExp 11 <*> parseExp 11
  <|> (\n x -> Cast (capture n x) I1 I2) <$ guard (p <= 10) <*> tokFw <*> parseExp 11 <*> parseExp 11
  <|> (\n x -> Cast (capture n x) I2 I1) <$ guard (p <= 10) <*> tokBw <*> parseExp 11 <*> parseExp 11
  <|> Free <$> parseNonOpName
  <|> Meta . TV.TV <$> tokMeta <*> parseMetaArgs
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
  go 12 lhs
 <|> do
  -- "{x:a} -> b"
  x <- tokLBrace *> parseExp 0 <* tokRBrace
  (op,po,pr) <- parseBinderOp Hidden 12 p
  y <- parseExp pr
  go po =<< op x y
 where
  go pcur x
      = do guard $ pcur >= 10 && p <= 10
           y <- tokLBrace *> parseExp 0 <* tokRBrace
           go 10 (AppH x y)
    <|> do (op,po,pr) <- parseOp pcur p
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
  guard $ pcur >= 11 && pmin <= 11
  tokHat
  return ((\x y -> pure (IV Blank Blank x y)), 11, 12)
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
 <|> do
  guard $ pcur >= 3 && pmin <= 2
  tokComma
  return ((\x y -> pure (Pair (Arg h x) y Blank)), 3,2)

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
mkOpBinder binder h a c = return $ Binder binder (Arg h a) (notBound c)

mkBinders :: Binder -> [NamedArg Exp] -> Exp -> Exp
mkBinders binder args c = foldr bind c args
  where
  bind :: NamedArg Exp -> Exp -> Exp
  bind (Arg h (Named n b)) v = Binder binder (Arg h b) (capture n v)

-- interpret an expression as a list of names
toNames :: Exp -> Parser [Name]
toNames (toName -> Just x) = return [x]
toNames (AppV xs (toName -> Just x)) = (++ [x]) <$> toNames xs
toNames x = fail $ showExp $ text "Left hand side of ':' should be a list of names, found" $/$ ppr 0 x

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

parseSumCtor :: Parser SumCtor
parseSumCtor = SumCtor <$> tokName <* tokColon <*> parseExp 0

parseSumCase :: Parser SumCase
parseSumCase = do
  n     <- tokName
  (m,x) <- (,) <$> tokName <*> pure Blank
       <|> (,) <$ tokLParen <*> tokName <* tokColon <*> parseExp 0 <* tokRParen
  tokArrow
  y <- parseExp 0
  return $ SumCase n x (capture m y)

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

parseExpTop :: Parser Exp
parseExpTop = (tokWS *> parseExp 0 <* eof)

pe :: String -> Exp
pe = testParser parseExpTop
pd :: String -> [Decl]
pd = testParser parseDecls

