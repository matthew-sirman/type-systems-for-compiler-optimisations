module Unit
    ( runUnitTests
    ) where

import Unit.Parser (parserUnitTests)

import Test.HUnit

allTests :: Test
allTests = test
    [ parserUnitTests
    ]

runUnitTests :: IO ()
runUnitTests = do
    putStrLn "Running all unit tests..."
    putStrLn ""
    runTestTT allTests
    putStrLn "Done"

