{
{-# LANGUAGE ScopedTypeVariables #-}

module Parser.Lexer 
    ( alexMonadScan , Token(..)
    , Alex(..)
    , AlexPosn(..)
    , alexGetInput
    , alexError
    , runAlex
    , Identifier(..)
    ) where

}

%wrapper "monad"

$digit = [0-9]
$alpha = [a-zA-Z]

tokens :-
    $white+                             ;
    "--".*                              ;
    let                                 { keyword KWlet }
    in                                  { keyword KWin }
    case                                { keyword KWcase }
    of                                  { keyword KWof }
    if                                  { keyword KWif }
    then                                { keyword KWthen }
    else                                { keyword KWelse }
    data                                { keyword KWdata }
    where                               { keyword KWwhere }

    "="                                 { symbol TokEq }
    "=="                                { symbol TokEqEq }
    "!="                                { symbol TokNeq }
    "<"                                 { symbol TokLessThan }
    ">"                                 { symbol TokGreaterThan }
    "<="                                { symbol TokLessEq }
    ">="                                { symbol TokGreaterEq }
    "+"                                 { symbol TokPlus }
    "-"                                 { symbol TokMinus }
    "*"                                 { symbol TokTimes }
    "/"                                 { symbol TokDivide }

    "("                                 { symbol TokOpenParen }
    ")"                                 { symbol TokCloseParen }
    "["                                 { symbol TokOpenBracket }
    "]"                                 { symbol TokCloseBracket }
    ":"                                 { symbol TokColon }
    "->"                                { symbol TokArrow }
    "?"                                 { symbol TokQuestion }
    "!"                                 { symbol TokOne }
    "-o"                                { symbol TokLinearArrow }
    "-+"                                { symbol TokRelevantArrow }
    "-c"                                { symbol TokAffineArrow }

    "::"                                { symbol TokCons }

    ","                                 { symbol TokComma }
    "|"                                 { symbol TokPipe }
    "\"                                 { symbol TokBackslash }

    [a-z \_] [$alpha $digit \_ \']*     { identifier TokLowerId }
    [A-Z] [$alpha $digit \_ \']*        { identifier TokUpperId }
    "@" [a-z \_] [$alpha $digit \_ \']* { identifier TokMultiplicityId }
    $digit+                             { numeric TokIntegerLit }
    $digit+\.$digit+                    { numeric TokRealLit }

    ";;"                                { symbol TokEndStmt }

{

type Identifier = String

data Token
    = KWlet                         -- let
    | KWin                          -- in
    | KWcase                        -- case
    | KWof                          -- of
    | KWif                          -- if
    | KWthen                        -- then
    | KWelse                        -- else
    | KWdata                        -- data
    | KWwhere                       -- where

    | TokEq                         -- =
    | TokEqEq                       -- ==
    | TokNeq                        -- !=
    | TokLessThan                   -- <
    | TokGreaterThan                -- >
    | TokLessEq                     -- <=
    | TokGreaterEq                  -- >=
    | TokPlus                       -- +
    | TokMinus                      -- -
    | TokTimes                      -- *
    | TokDivide                     -- /

    | TokOpenParen                  -- (
    | TokCloseParen                 -- )
    | TokOpenBracket                -- [
    | TokCloseBracket               -- ]
    | TokColon                      -- :
    | TokArrow                      -- ->
    | TokQuestion                   -- ?
    | TokOne                        -- !
    | TokLinearArrow                -- -o
    | TokRelevantArrow              -- -+
    | TokAffineArrow                -- -c
    
    | TokCons                       -- ::

    | TokComma                      -- ,
    | TokPipe                       -- |
    | TokBackslash                  -- \

    | TokLowerId Identifier         -- [a-z_][a-zA-Z_'']*
    | TokUpperId Identifier         -- [A-Z][a-zA-Z_'']*
    | TokMultiplicityId Identifier  -- @[a-z_][a-zA-Z_'']*

    | TokIntegerLit Integer         -- [0-9]+
    | TokRealLit Double             -- [0-9]+\.[0-9]+

    | TokEndStmt                    -- ;;

    | TokEOF deriving Show

keyword, symbol :: Token -> AlexInput -> Int -> Alex Token
keyword t _ _ = pure t
symbol t _ _ = pure t

identifier :: (String -> Token) -> AlexInput -> Int -> Alex Token
identifier t (_, _, _, input) len = pure $ t (take len input)

numeric :: forall a. Read a => (a -> Token) -> AlexInput -> Int -> Alex Token
numeric t (_, _, _, input) len = pure $ t (read (take len input) :: a)

alexEOF = pure TokEOF

}

