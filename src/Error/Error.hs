module Error.Error (
    showContext
    ) where

-- Error message pretty printing

import Parser.AST (SourceLocation(..))

import Data.List (intercalate)

showContext :: String -> SourceLocation -> String
showContext text loc = intercalate "\n" (findLines (slStart loc) (slEnd loc) lengthLines) ++ "\n" ++ show loc
    where
        lengthLines :: [(Int, String)]
        lengthLines = map (\line -> (length line + 1, line)) (lines text)

        findLines :: Int -> Int -> [(Int, String)] -> [String]
        findLines _ _ [] = []
        findLines start end ((size, line):lines)
            | start' < 0 && end >= 0 = line : highlightLine : findLines start' end' lines
            | end < 0 = []
            | otherwise = findLines start' end' lines
            where
                start', end' :: Int
                start' = start - size
                end' = end - size

                highlightLine = replicate start ' ' ++ replicate (min end (size - 1) - max 0 start) '^'

