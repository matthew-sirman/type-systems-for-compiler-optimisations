module Main where

import Parser.Parser
import Parser.AST
import Preprocessor.Preprocessor
import Typing.Checker
import Typing.Types
import Compiler.Compiler
import Compiler.Bytecode
import Interpreter.Interpreter
import Builtin.Builtin

import System.Environment
import Control.Monad.Except

import Debug.Trace

data Options = Options
    { sourceFile :: FilePath
    , interpreterSettings :: InterpreterSettings
    }

type Process a = ExceptT String IO a

settings :: InterpreterSettings
settings = defaultSettings
    { _debug = True
    , _showExecInstruction = False
    , _showBytecode = False
    }

getOptions :: Process Options
getOptions = do
    args <- liftIO getArgs
    case args of
      (source:_) -> pure $ Options source settings
      _ -> do
          throwError "Source file argument required."

readSourceFile :: Options -> Process String
readSourceFile opt = liftIO $ readFile (sourceFile opt)

parseSource :: String -> Process [Loc Statement]
parseSource source =
    case parse source of
      Left e -> throwError e
      Right stmts -> pure stmts

preprocess :: String -> Process (Loc ValExpr, StaticContext)
preprocess source = do
    stmts <- parseSource source
    case transformAST stmts defaultBuiltins of
      Left e -> throwError (showPPError source e)
      Right expr -> pure expr

runTypeChecker :: String -> StaticContext -> Loc ValExpr -> Process (TypedExpr, MultiplicityPoset)
runTypeChecker source ctx ve = do
    case typecheck ctx ve of
      Left (e, tvm) -> throwError (showError source tvm e)
      Right (t, ps) -> pure (t, ps)

compileProgram :: StaticContext -> MultiplicityPoset -> TypedExpr -> Process Program
compileProgram staticContext ps expr = do
    pure (compile staticContext ps expr)

generate :: Program -> Process Bytecode
generate program =
    pure (generateBytecode program)

executeBytecode :: Options -> Bytecode -> Process ()
executeBytecode opt bytecode =
    liftIO $ interpret (interpreterSettings opt) bytecode

pipeline :: Process ()
pipeline = do
    opt <- getOptions
    source <- readSourceFile opt
    (expr, ctx) <- preprocess source
    (typedExpr, ps) <- runTypeChecker source ctx expr
    program <- compileProgram ctx ps typedExpr
    liftIO $ print program
    bytecode <- generate program
    executeBytecode opt bytecode

main :: IO ()
main = do
    result <- runExceptT pipeline
    case result of
      Left err -> do
          putStrLn "Error(s) encountered:"
          putStrLn err
      Right () -> pure ()

