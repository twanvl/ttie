{-# LANGUAGE FlexibleInstances, FlexibleContexts, UndecidableInstances, MultiParamTypeClasses #-}
module Main where

import Prelude ()
import Util.MyPrelude
import Util.PrettyM
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

--------------------------------------------------------------------------------
-- Statements
--------------------------------------------------------------------------------

data Statement
  = TypeSignature Name Exp
  | FunBody Name Exp
  | PrintType Exp
  | PrintEval EvalStrategy Exp
  | PrintEnv
  | CheckEqual Exp Exp
  | Import FilePath
  | Help
  | ClearEnv

instance (MonadBoundNames m, MonadBound Exp m) => Pretty m Statement where
  ppr _ (TypeSignature n x) = text n <+> text ":" <+> ppr 0 x
  ppr _ (FunBody n x) = text n <+> text "=" <+> ppr 0 x
  ppr _ (PrintType x) = text ":type" <+> ppr 0 x
  ppr _ (PrintEval _ x) = text ":eval" <+> ppr 0 x
  ppr _ (PrintEnv) = text ":env"
  ppr _ (CheckEqual x y) = text ":check" <+> ppr 0 x <+> text "=" <+> ppr 0 y
  ppr _ (Import x) = text ":import" <+> ppr 0 x
  ppr _ (Help) = text ":help"
  ppr _ (ClearEnv) = text ":clear"

parseStmt :: Parser Statement
parseStmt
    = PrintType      <$ (tokReservedName "type" <|> tokReservedName ":type" <|> tokReservedName ":t") <*> parseExp 0
  <|> PrintEval WHNF <$ (tokReservedName "eval" <|> tokReservedName ":eval") <*> parseExp 0
  <|> PrintEval NF   <$ tokReservedName ":nf"   <*> parseExp 0
  <|> PrintEnv       <$ tokReservedName ":env"
  <|> CheckEqual     <$ (tokReservedName "check" <|> tokReservedName ":check")  <*> parseExp 0 <* tokEquals <*> parseExp 0
  <|> Import         <$ (tokReservedName "import" <|> tokReservedName ":l") <*> tokPath
  <|> Help           <$ (tokReservedName ":help" <|> tokReservedName ":?")
  <|> ClearEnv       <$ tokReservedName ":clear"
  <|> do
        n <- tokName 
        id (TypeSignature n <$ tokColon <*> parseExp 0) <|>
           (FunBody       n <$ tokEquals <*> parseExp 0)

parseStmts :: Parser [Statement]
parseStmts = withIndentation (many $ parseStmt0) <* tokWS <* eof
  where
  parseStmt0 = try (tokWS >> notIndented) >> withIndentation parseStmt

--------------------------------------------------------------------------------
-- Running statements
--------------------------------------------------------------------------------

type Env = Map Name Decl

reportErrors :: MonadIO m => ExceptT Doc m () -> m ()
reportErrors mx = do
  ex <- runExceptT mx
  case ex of
    Left  e -> liftIO $ putStrLn $ show e
    Right x -> return x

runTcMIO :: EvalAllMetas a => TcM a -> ExceptT Doc (StateT Env IO) a
runTcMIO mx = do
  env <- get
  let ctx = emptyCtx { ctxDecls = env }
  case runTcM ctx (mx >>= evalAllMetasThrow) of
    Left e -> throwError e
    Right x -> return x

runStmt :: Statement -> StateT Env IO ()
runStmt (TypeSignature name typ) = reportErrors $ do
  (typ',_) <- runTcMIO (tcType typ)
  env <- get
  case Map.lookup name env of
    Nothing -> modify $ Map.insert name (Postulate typ')
    Just _  -> throwError =<< text "Name already defined:" <+> text name
runStmt (FunBody name exp) = reportErrors $ do
  env <- get
  ty <- case Map.lookup name env of
    Nothing -> return Nothing
    Just (Postulate ty) -> return $ Just ty
    Just _ -> throwError =<< text "Name already defined:" <+> text name
  (exp',ty') <- runTcMIO (tc ty exp)
  modify $ Map.insert name (FunDecl ty' exp')
runStmt (PrintType exp) = reportErrors $ do
  (_,ty') <- runTcMIO (tc Nothing exp)
  liftIO $ putStrLn $ show ty'
runStmt (PrintEval s exp) = reportErrors $ do
  exp' <- runTcMIO $ tcEval s . fst =<< tc Nothing exp
  liftIO $ putStrLn $ show exp'
runStmt (PrintEnv) = do
  env <- get
  forM_ (Map.toList env) $ \(n,t) ->
    lift . putStrLn . show $ runIdentity . runNamesT $ pprDecl n t
runStmt (CheckEqual a b) = reportErrors $ do
  (a',b') <- runTcMIO $ do
    (a',ta) <- tc Nothing a
    (b',tb) <- tc Nothing b
    _ <- unify ta tb
    return (a',b')
  _ <- runTcMIO $ unify a' b'
  return ()
runStmt (Import file) = parseFile fileName
  where
  fileName
    | any (`elem` "./") file = file
    | otherwise = file ++ ".tt2"
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
  put Map.empty

--------------------------------------------------------------------------------
-- Main function
--------------------------------------------------------------------------------

-- parse and run a bunch of statements from a file
parseFile :: FilePath -> StateT Env IO ()
parseFile file = do
  contents <- lift $ readFile file
  case runParser parseStmts file contents of
    Left e -> lift $ putStrLn $ "Error: " ++ show e
    Right stmts -> mapM_ runStmt stmts

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
       <> O.header "tt2 - A simple type checker/evaluator for a type theory with indexed equality"
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
  flip evalStateT Map.empty $ do
    maybe (return ()) parseFile $ optsFile opts
    repl


{-
-- typecheck a file
main :: IO ()
main = execParser opts >>= mainWithargs
  where
  opts = info (helper <*> sample)
      ( fullDesc
     <> progDesc ""
     <> header "tt2 - A simple type checker/evaluator for a type theory with indexed equality" )
-}

{-
Example:

foo : Nat -> Nat
foo = suc

:typeof foo
:eval   foo
:check  foo = bar

-}
