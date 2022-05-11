module Main where

import Parser.Parser
import Parser.AST
import Preprocessor.Preprocessor
import Typing.Checker
import Typing.Types
import Compiler.Translate
import Compiler.Compiler
import Compiler.Bytecode
import Interpreter.Interpreter
import Builtin.Builtin

import System.Environment
import Control.Monad.Except

import Debug.Trace
import qualified IR.Program as IR

data Options = Options
    { sourceFile :: FilePath
    , showCore :: Bool
    , showIR :: Bool
    , interpreterSettings :: InterpreterSettings
    }

type Process a = ExceptT String IO a

settings :: InterpreterSettings
settings = defaultSettings
    { _debug = False
    , _showExecInstruction = False
    , _showBytecode = False
    }

getOptions :: Process Options
getOptions = do
    args <- liftIO getArgs
    case args of
      (source:args) ->
          let opts = Options
                         { sourceFile = source
                         , showCore = "--show-core" `elem` args
                         , showIR = "--show-ir" `elem` args
                         , interpreterSettings = settings 
                             { _outputCsv = "--output-csv" `elem` args
                             , _debug = "--show-stats" `elem` args
                             }
                         }
           in pure opts
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

convertToCore :: StaticContext -> MultiplicityPoset -> TypedExpr -> Process CodegenExpr
convertToCore staticContext ps expr =
    pure (convertAST staticContext ps expr)

compileProgram :: StaticContext -> MultiplicityPoset -> CodegenExpr -> Process Program
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
    core <- convertToCore ctx ps typedExpr
    when (showCore opt) $ liftIO $ print core
    program <- compileProgram ctx ps core
    when (showIR opt) $ liftIO $ print program
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

