module Main where

import Parser.Parser
import Parser.AST
import Typing.Checker
import Typing.Types

import System.Environment
import Control.Monad.Except

newtype Options = Options
    { sourceFile :: FilePath
    }

type Process a = ExceptT String IO a

getOptions :: Process Options
getOptions = do
    args <- liftIO getArgs
    case args of
      (source:_) -> pure $ Options source
      _ -> do
          throwError "Source file argument required."

readSourceFile :: Options -> Process String
readSourceFile opt = liftIO $ readFile (sourceFile opt)

parseSource :: String -> Process (Loc ValExpr)
parseSource source = case test_parseExpr source of
                     Left e -> throwError e
                     Right ve -> pure ve

runTypeChecker :: String -> Process ()
runTypeChecker source = do
    ve <- parseSource source
    case typecheck ve of
      Left (e, tvm) -> throwError (showError source tvm e)
      Right t -> lift $ print t

pipeline :: Process ()
pipeline = do
    opt <- getOptions
    source <- readSourceFile opt
    runTypeChecker source

main :: IO ()
main = do
    result <- runExceptT pipeline
    case result of
      Left err -> do
          putStrLn "Error(s) encountered:"
          putStrLn err
      Right () -> do
          putStrLn ""
          putStrLn "Success"

