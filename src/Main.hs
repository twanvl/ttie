{-# LANGUAGE FlexibleInstances, FlexibleContexts, UndecidableInstances, MultiParamTypeClasses #-}
{-# LANGUAGE TemplateHaskell, RankNTypes #-}
module Main where

import Prelude ()
import Util.MyPrelude
import Util.PrettyM hiding ((<.>))
import Util.Parser
import Names
import Tokenizer
import Syntax
import Typing
import TcMonad
import Eval

import qualified Options.Applicative as O
import qualified Data.Map as Map
import Control.Monad.Trans
import System.IO
import System.Directory
import System.FilePath
import Lens.Simple

--------------------------------------------------------------------------------
-- Statements
--------------------------------------------------------------------------------

data Statement
  = TypeSignature Name Exp
  | FunBody Name Exp
  | PrintType EvalStrategy Exp
  | PrintEval EvalStrategy Exp
  | PrintEnv
  | CheckEqual Exp Exp
  | Import FilePath
  | Help
  | ClearEnv

instance (MonadBoundNames m, MonadBound Exp m) => Pretty m Statement where
  ppr _ (TypeSignature n x) = text n <+> text ":" <+> ppr 0 x
  ppr _ (FunBody n x) = text n <+> text "=" <+> ppr 0 x
  ppr _ (PrintType _ x) = text ":type" <+> ppr 0 x
  ppr _ (PrintEval _ x) = text ":eval" <+> ppr 0 x
  ppr _ (PrintEnv) = text ":env"
  ppr _ (CheckEqual x y) = text ":check" <+> ppr 0 x <+> text "=" <+> ppr 0 y
  ppr _ (Import x) = text ":import" <+> ppr 0 x
  ppr _ (Help) = text ":help"
  ppr _ (ClearEnv) = text ":clear"

parseStmt :: Parser Statement
parseStmt
    = PrintType NoEval <$ (tokReservedName "type" <|> tokReservedName ":type" <|> tokReservedName ":t") <*> parseExp 0
  <|> PrintType NF     <$ (tokReservedName ":nftype" <|> tokReservedName ":tnf") <*> parseExp 0
  <|> PrintEval WHNF   <$ (tokReservedName "eval" <|> tokReservedName ":eval") <*> parseExp 0
  <|> PrintEval NF     <$ tokReservedName ":nf"   <*> parseExp 0
  <|> PrintEnv         <$ tokReservedName ":env"
  <|> CheckEqual       <$ (tokReservedName "check" <|> tokReservedName ":check")  <*> parseExp 0 <* tokEquals <*> parseExp 0
  <|> Import           <$ (tokReservedName "import" <|> tokReservedName ":l") <*> tokPath
  <|> Help             <$ (tokReservedName ":help" <|> tokReservedName ":?")
  <|> ClearEnv         <$ tokReservedName ":clear"
  <|> do
        n <- tokName 
        id (TypeSignature n <$ tokColon <*> parseExp 0) <|>
           (FunBody       n <$ tokEquals <*> parseExp 0)

parseStmts :: Parser [Statement]
parseStmts = withIndentation (many $ parseStmt0) <* tokWS <* eof
  where
  parseStmt0 = try (tokWS >> notIndented) >> withIndentation parseStmt

--------------------------------------------------------------------------------
-- State/environment of the interpreter
--------------------------------------------------------------------------------

data Env = Env
  { _envNames :: Map Name Decl
  , _envWorkingDir :: Maybe FilePath
  }
$(makeLenses ''Env)

emptyEnv :: Env
emptyEnv = Env
  { _envNames = Map.empty
  , _envWorkingDir = Nothing
  }

withWorkingDir :: FilePath -> StateT Env IO () -> StateT Env IO ()
withWorkingDir = withFieldValue envWorkingDir . Just

withFieldValue :: Monad m => Lens' s a -> a -> StateT s m b -> StateT s m b
withFieldValue field newValue action = do
  oldValue <- use field
  assign field newValue
  out <- action
  assign field oldValue
  return out

--------------------------------------------------------------------------------
-- Running statements
--------------------------------------------------------------------------------

reportErrors :: MonadIO m => ExceptT Doc m () -> m ()
reportErrors mx = do
  ex <- runExceptT mx
  case ex of
    Left  e -> liftIO $ putStrLn $ show e
    Right x -> return x

runTcMIO :: EvalAllMetas a => TcM a -> ExceptT Doc (StateT Env IO) a
runTcMIO mx = do
  names <- use envNames
  let ctx = emptyCtx { ctxDecls = names }
  case runTcM ctx (mx >>= evalAllMetasThrow) of
    Left e -> throwError e
    Right x -> return x

runStmt :: Statement -> StateT Env IO ()
runStmt (TypeSignature name typ) = reportErrors $ do
  (typ',_) <- runTcMIO (tcType typ)
  names <- use envNames
  case Map.lookup name names of
    Nothing -> envNames %= Map.insert name (Postulate typ')
    Just _  -> throwError =<< text "Name already defined:" <+> text name
runStmt (FunBody name exp) = reportErrors $ do
  names <- use envNames
  ty <- case Map.lookup name names of
    Nothing -> return Nothing
    Just (Postulate ty) -> return $ Just ty
    Just _ -> throwError =<< text "Name already defined:" <+> text name
  (exp',ty') <- runTcMIO (tc ty exp)
  envNames %= Map.insert name (FunDecl ty' exp')
runStmt (PrintType s exp) = reportErrors $ do
  ty' <- runTcMIO (tc Nothing exp >>= tcEval s . snd)
  liftIO $ putStrLn $ show ty'
runStmt (PrintEval s exp) = reportErrors $ do
  exp' <- runTcMIO $ tcEval s . fst =<< tc Nothing exp
  liftIO $ putStrLn $ show exp'
runStmt (PrintEnv) = do
  names <- use envNames
  forM_ (Map.toList names) $ \(n,t) ->
    lift . putStrLn . show $ runIdentity . runNamesT $ pprDecl n t
runStmt (CheckEqual a b) = reportErrors $ do
  (a',b') <- runTcMIO $ do
    (a',ta) <- tc Nothing a
    (b',tb) <- tc Nothing b
    _ <- unify ta tb
    return (a',b')
  _ <- runTcMIO $ unify a' b'
  return ()
runStmt (Import file) = parseModule file
runStmt (Help) = do
  lift $ putStrLn "x = e          Add a definition"
  lift $ putStrLn "x : e          Add a postulate"
  lift $ putStrLn ":check x = y   Check that two expressions are equal"
  lift $ putStrLn ":type x        Print the type of x"
  lift $ putStrLn ":eval x        Print the WHNF evaluation of x"
  lift $ putStrLn ":nf x          Print the NF evaluation of x"
  lift $ putStrLn ":help          Show help message"
  lift $ putStrLn ":clear         Clear the environment"
runStmt (ClearEnv) = do
  put emptyEnv

--------------------------------------------------------------------------------
-- Main function
--------------------------------------------------------------------------------

-- parse and run a bunch of statements from a file
parseFile :: FilePath -> StateT Env IO ()
parseFile file = do
  contents <- lift $ readFile file
  case runParser parseStmts file contents of
    Left e -> lift $ putStrLn $ "Error: " ++ show e
    Right stmts ->
      withWorkingDir (takeDirectory file) $
        mapM_ runStmt stmts

parseModule :: String -> StateT Env IO ()
parseModule moduleName = do
  dir <- use envWorkingDir
  let files = [ prefix $ suffix $ moduleName
              | suffix <- [id, (<.> "ttie")]
              , prefix <- [id] ++ [(wdir </>) | Just wdir <- [dir]] ]
      go (file:fs) = do
        exist <- lift $ doesFileExist file
        if exist then parseFile file else go fs
      go [] = lift $ putStrLn $ "Error: Module does not exist: " ++ moduleName
  go files

repl :: StateT Env IO ()
repl = do
  lift $ putStr "> "
  lift $ hFlush stdout
  line <- lift getLine
  replCommand line

replCommand :: String -> StateT Env IO ()
replCommand cmd | cmd `elem` [":q",":quit"] = return ()
replCommand "" = repl
replCommand cmd
  | otherwise = do
      case runParser (parseStmt <* tokWS <* eof) "input" cmd of
        Left e -> lift $ putStrLn $ "Error: " ++ show e
        Right x -> runStmt x
      repl


data Options = Options
  { optsFile :: Maybe String
  }

main :: IO ()
main = O.execParser opts >>= mainWithOptions
  where
  opts = O.info (O.helper <*> options)
         (O.fullDesc
       <> O.header "ttie - A simple type checker/evaluator for a type theory with indexed equality"
       <> O.progDesc "REPL loading the given file")
  options = Options
    <$> O.argument (Just <$> O.str)
        ( O.metavar "FILE"
       <> O.help "File to open"
       <> O.value Nothing)

mainWithOptions :: Options -> IO ()
mainWithOptions opts = do
  hSetBuffering stdout LineBuffering
  hSetBuffering stdin LineBuffering
  flip evalStateT emptyEnv $ do
    maybe (return ()) parseModule $ optsFile opts
    repl

