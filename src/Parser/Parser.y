{
module Parser.Parser 
    ( parse
    , parseType

    , test_parseStmt
    , test_parseExpr
    , test_parseDatatype
    , test_parseType
    , test_parsePattern
    ) where

import Parser.Lexer
import Parser.AST

import qualified Data.List.NonEmpty as NE
import Data.Maybe (fromJust)
}

%name alexParser program
%name alexTypeParser type

%name test_alexStmtParser stmt
%name test_alexExprParser expr
%name test_alexTypeParser type
%name test_alexDatatypeParser datatype
%name test_alexPatternParser pattern

%tokentype { Loc Token }
%error { parseError }
%monad { Alex }
%lexer { lexer } { L _ TokEOF }
%expect 22

%token
    import              { L _ DImport }
    '.'                 { L _ DDot }
    let                 { L _ KWlet }
    and                 { L _ KWand }
    in                  { L _ KWin }
    case                { L _ KWcase }
    of                  { L _ KWof }
    if                  { L _ KWif }
    then                { L _ KWthen }
    else                { L _ KWelse }
    data                { L _ KWdata }
    where               { L _ KWwhere }

    '='                 { L _ TokEq }
    '=='                { L _ TokEqEq }
    '!='                { L _ TokNeq }
    '<'                 { L _ TokLessThan }
    '>'                 { L _ TokGreaterThan }
    '<='                { L _ TokLessEq }
    '>='                { L _ TokGreaterEq }
    '+'                 { L _ TokPlus }
    '-'                 { L _ TokMinus }
    '*'                 { L _ TokTimes }
    '/'                 { L _ TokDivide }

    '('                 { L _ TokOpenParen }
    ')'                 { L _ TokCloseParen }
    '['                 { L _ TokOpenBracket }
    ']'                 { L _ TokCloseBracket }
    ':'                 { L _ TokColon }
    '->'                { L _ TokArrow }
    '?'                 { L _ TokQuestion }
    '!'                 { L _ TokOne }
    '-o'                { L _ TokLinearArrow }
    '-+'                { L _ TokRelevantArrow }
    '-c'                { L _ TokAffineArrow }

    '::'                { L _ TokCons }

    ','                 { L _ TokComma }
    '|'                 { L _ TokPipe }
    ';'                 { L _ TokSemiColon }
    '\\'                { L _ TokBackslash }

    ivar                { L _ (TokInfixId _) }
    lvar                { L _ (TokLowerId _) }
    uvar                { L _ (TokUpperId _) }
    mvar                { L _ (TokMultiplicityId _) }
    int                 { L _ (TokIntegerLit _) }
    real                { L _ (TokRealLit _) }

    ';;'                { L _ TokEndStmt }

%right in '::'
%nonassoc '<' '>' '<=' '>=' '==' '!='
%left '+' '-'
%left '*' '/'
%left NEGATE

%%

program :: { [Loc Statement] }
    : stmts                                             { reverse $1 }

stmts :: { [Loc Statement] }
    : {- empty -}                                       { [] }
    | stmts stmt                                        { $2 : $1 }

stmt :: { Loc Statement }
    : import import_name ';;'                           { loc (Import $2) $1 $> }
    | lvar ':' type ';;'                                { loc (TypeDecl (idTok $1) $3) $1 $> }
    | '(' infix_op ')' ':' type ';;'                    { loc (TypeDecl $2 $5) $1 $> }
    | lvar seq(pattern) '=' expr ';;'                   { loc (makeFuncDecl (idTok $1) $2 $4) $1 $> }
    | pattern infix_op pattern '=' expr ';;'            { loc (makeFuncDecl $2 [$1, $3] $5) $1 $> }
    | datatype ';;'                                     { loc (TypeDef $1) $1 $> }

expr :: { Loc ValExpr }
    : let let_binding_list in expr                      { loc (VELet (reverse $2) $4) $1 $> }
    | case maybe(multiplicity) expr of case_branches    { loc (VECase $2 $3 (NE.reverse $5)) $1 (NE.last $>) }
    | if maybe(multiplicity) expr then expr else expr   { loc (makeIfCase $2 $3 $5 $7) $1 $> }
    | '\\' annotated(pattern) arrow expr                { loc (VELambda $2 $3 $4) $1 $> }
    | term                                              { $1 }

term :: { Loc ValExpr }
    : term infix_op term                                { loc (makeBinOp $1 (VEVar <\$> $2) $3) $1 $> }
    | apps                                              { $1 }

apps :: { Loc ValExpr }
    : apps atom                                         { loc (VEApp $1 $2) $1 $> }
    | atom                                              { $1 }

atom :: { Loc ValExpr }
    : '(' expr ')'                                      { $2 }
    | lvar                                              { loc (VEVar (rawId $1)) $1 $> }
    | uvar                                              { loc (VEVar (rawId $1)) $1 $> }
    | int                                               { loc (VELiteral (IntLiteral (intTok $1))) $1 $> }
    | real                                              { loc (VELiteral (RealLiteral (realTok $1))) $1 $> }
    | '(' ')'                                           { loc (VEVar (I "()")) $1 $> }
    | tuple(expr)                                       { (VELiteral . TupleLiteral) <\$> $1 }
    | list(expr)                                        { (VELiteral . ListLiteral) <\$> $1 }

infix_op :: { Loc Identifier }
    : '=='                                              { loc (I "==") $1 $> }
    | '!='                                              { loc (I "!=") $1 $> }
    | '<'                                               { loc (I "<") $1 $> }
    | '>'                                               { loc (I ">") $1 $> }
    | '<='                                              { loc (I "<=") $1 $> }
    | '>='                                              { loc (I ">=") $1 $> }
    | '+'                                               { loc (I "+") $1 $> }
    | '-'                                               { loc (I "-") $1 $> }
    | '*'                                               { loc (I "*") $1 $> }
    | '/'                                               { loc (I "/") $1 $> }
    | '::'                                              { loc (I "::") $1 $> }
    | ivar                                              { loc (rawId $1) $1 $> }

datatype :: { Loc TypeDefinition }
    : data uvar seq(lvar) seq(mvar)                     { makeTypeDef $1 (idTok $2) (idTok <\$> $3) (idTok <\$> $4) [] }
    | data uvar seq(lvar) seq(mvar) where constructors  { makeTypeDef $1 (idTok $2) (idTok <\$> $3) (idTok <\$> $4) $6 }

constructors :: { [Loc (Annotated Identifier)] }
    : constructor seq(constructor)                      { $1 : $2 }

constructor :: { Loc (Annotated Identifier) }
    : '|' uvar ':' type                                 { loc (Annotated (idTok $2) (Just $4)) $1 $> }

list(p)
    : '[' list_list(p) ']'                              { loc (reverse $2) $1 $> }

list_list(p)
    : {- empty -}                                       { [] }
    | p                                                 { [$1] }
    | list_list(p) ',' p                                { $3 : $1 }

seq(p)
    : seq_list(p)                                       { reverse $1 }

seq_list(p)
    : {- empty -}                                       { [] }
    | seq_list(p) p                                     { $2 : $1 }

let_binding_list :: { [Loc LetBinding] }
    : let_binding                                       { [$1] }
    | let_binding_list and let_binding                  { $3 : $1 }

let_binding :: { Loc LetBinding }
    : maybe(multiplicity) annotated(pattern)
        seq(pattern) '=' expr                           { makeLetBinding $1 $2 (transformLambdas $5 $3) }

annotated(p)
    : p                                                 { loc (Annotated $1 Nothing) $1 $> }
    | p ':' type                                        { loc (Annotated $1 (Just $3)) $1 $> }
    | '(' annotated(p) ')'                              { $2 }

case_branches :: { NE.NonEmpty (Loc CaseBranch) }
    : case_branch                                       { $1 NE.:| [] }
    | case_branches ';' case_branch                     { $3 NE.<| $1 }

case_branch :: { Loc CaseBranch }
    : pattern '->' expr                                 { loc (CaseBranch $1 $3) $1 $> }

pattern_list :: { [Loc SourcePattern] }
    : pattern                                           { [$1] }
    | pattern pattern_list                              { $1 : $2 }

pattern :: { Loc SourcePattern }
    : uvar                                              { loc (ConsPattern (rawId $1) []) $1 $> }
    | '(' uvar pattern seq(pattern) ')'                 { loc (ConsPattern (rawId $2) ($3:$4)) $1 $> }
    | '(' pattern '::' pattern ')'                      { loc (ConsPattern (I "::") [$2, $4]) $1 $> }
    | pattern_atom                                      { $1 }

pattern_atom :: { Loc SourcePattern }
    : int                                               { loc (LitPattern (IntLiteral (intTok $1))) $1 $> }
    | real                                              { loc (LitPattern (RealLiteral (realTok $1))) $1 $> }
    | tuple(pattern)                                    { (LitPattern . TupleLiteral) <\$> $1 }
    | list(pattern)                                     { (LitPattern . ListLiteral) <\$> $1 }
    | lvar                                              { loc (VarPattern (rawId $1)) $1 $> }
    | '(' pattern ')'                                   { $2 }

type :: { Loc TypeExpr }
    : type_apps arrow type                              { loc (TEArrow $1 $2 $3) $1 $> }
    | type_apps                                         { $1 }

type_apps :: { Loc TypeExpr }
    : type_apps type_atom                               { loc (TEApp $1 $2) $1 $> }
    | type_atom                                         { $1 }

type_atom :: { Loc TypeExpr }
    : uvar                                              { loc (TEGround (rawId $1)) $1 $> }
    | lvar                                              { loc (TEPoly (rawId $1)) $1 $> }
    | '(' ')'                                           { loc TEUnit $1 $> }
    | tuple(type)                                       { TETuple <\$> $1 }
    | '[' type ']'                                      { loc (TEList $2) $1 $> }
    | '(' type ')'                                      { $2 }

tuple(p)
    : '(' tuple_list(p) ')'                             { loc (reverse $2) $1 $> }

tuple_list(p)
    : p ',' p                                           { [$3, $1] }
    | tuple_list(p) ',' p                               { $3 : $1 }

arrow :: { Loc ArrowExpr }
    : '->'                                              { loc (makeArrow Normal $1) $1 $> }
    | '-o'                                              { loc (makeArrow Linear $1) $1 $> }
    | '-+'                                              { loc (makeArrow Relevant $1) $1 $> }
    | '-c'                                              { loc (makeArrow Affine $1) $1 $> }
    | '->' multiplicity                                 { loc (ArrowExpr (Just $2)) $1 $> }

multiplicity :: { Loc MultiplicityExpr }
    : mvar                                              { loc (MEPoly (rawId $1)) $1 $> }
    | '*'                                               { loc (MEAtom Normal) $1 $> }
    | '!'                                               { loc (MEAtom Linear) $1 $> }
    | '+'                                               { loc (MEAtom Relevant) $1 $> }
    | '?'                                               { loc (MEAtom Affine) $1 $> }

maybe(p)
    : {- empty -}                                       { Nothing }
    | p                                                 { Just $1 }

import_name :: { Loc [String] }
import_name
    : uvar                                              { loc [plainFileString $1] $1 $> }
    | uvar '.' import_name                              { loc (plainFileString $1 : syntax $3) $1 $> }

{

idTok :: Loc Token -> Loc Identifier
idTok (L sl (TokLowerId name)) = L sl name
idTok (L sl (TokUpperId name)) = L sl name
idTok (L sl (TokMultiplicityId name)) = L sl name

rawId :: Loc Token -> Identifier
rawId (L _ (TokInfixId name)) = name
rawId (L _ (TokLowerId name)) = name
rawId (L _ (TokUpperId name)) = name
rawId (L _ (TokMultiplicityId name)) = name

plainFileString :: Loc Token -> String
plainFileString (L _ (TokUpperId (I name))) = name

intTok :: Loc Token -> Int
intTok (L _ (TokIntegerLit i)) = i

realTok :: Loc Token -> Double
realTok (L _ (TokRealLit r)) = r

makeFuncDecl :: Loc Identifier -> [Loc SourcePattern] -> Loc ValExpr -> Statement
makeFuncDecl name patterns expr = FuncDecl name (transformLambdas expr patterns)

transformLambdas :: Loc ValExpr -> [Loc SourcePattern] -> Loc ValExpr
transformLambdas base [] = base
transformLambdas base (p@(L sl _):ps) = L sl $ VELambda (L sl (Annotated p Nothing)) (L sl (ArrowExpr Nothing)) (transformLambdas base ps)

makeTypeDef :: Loc Token -> Loc Identifier -> [Loc Identifier] -> [Loc Identifier] -> [Loc (Annotated Identifier)] -> Loc TypeDefinition
makeTypeDef start name pVars mVars cs
    | not (null cs) = def (last cs)
    | not (null mVars) = def (last mVars)
    | not (null pVars) = def (last pVars)
    | otherwise = def name
    where
        def :: Loc a -> Loc TypeDefinition
        def end = loc (TypeDefinition name pVars mVars cs) start end

makeIfCase :: Maybe (Loc MultiplicityExpr) -> Loc ValExpr -> Loc ValExpr -> Loc ValExpr -> ValExpr
makeIfCase m cond ifT@(L trueLoc _) ifF@(L falseLoc _) = VECase m cond (thenBranch NE.:| [elseBranch])
    where
        thenBranch = L trueLoc (CaseBranch (L trueLoc (ConsPattern (I "True") [])) ifT)
        elseBranch = L falseLoc (CaseBranch (L falseLoc (ConsPattern (I "False") [])) ifF)

makeBinOp :: Loc ValExpr -> Loc ValExpr -> Loc ValExpr -> ValExpr
makeBinOp lhs op rhs = VEApp (loc (VEApp op lhs) lhs op) rhs

makeLetBinding :: Maybe (Loc MultiplicityExpr) -> Loc (Annotated SourcePattern) -> Loc ValExpr -> Loc LetBinding
makeLetBinding Nothing pattern expr = loc (LetBinding Nothing pattern expr) pattern expr
makeLetBinding m@(Just start) pattern expr = loc (LetBinding m pattern expr) start expr

makeArrow :: MultiplicityAtom -> Loc a -> ArrowExpr
makeArrow atom (L sl _) = ArrowExpr (Just (L sl (MEAtom atom)))

lexer :: (Loc Token -> Alex a) -> Alex a
lexer cont = do
    tok <- alexMonadScan
    cont tok

parseError :: Loc Token -> Alex a
parseError (L _ t) = do
    ((AlexPn _ line column), _, _, _) <- alexGetInput
    alexError ("parser error at line " ++ (show line) ++ ", column " ++ (show column) ++ ". Unexpected token " ++ (show t) ++ ".")

getSourceLocation :: Alex Int
getSourceLocation = do
    ((AlexPn loc _ _), _, _, _) <- alexGetInput
    pure loc

getLineNumber :: Alex Int
getLineNumber = do
    ((AlexPn _ line _), _, _, _) <- alexGetInput
    pure line

parse :: String -> Either String [Loc Statement]
parse s = runAlex s alexParser

parseType :: String -> Either String (Loc TypeExpr)
parseType s = runAlex s alexTypeParser

test_parseStmt :: String -> Either String (Loc Statement)
test_parseStmt s = runAlex s test_alexStmtParser

test_parseExpr :: String -> Either String (Loc ValExpr)
test_parseExpr s = runAlex s test_alexExprParser

test_parseDatatype :: String -> Either String (Loc TypeDefinition)
test_parseDatatype s = runAlex s test_alexDatatypeParser

test_parseType :: String -> Either String (Loc TypeExpr)
test_parseType s = runAlex s test_alexTypeParser

test_parsePattern :: String -> Either String (Loc SourcePattern)
test_parsePattern s = runAlex s test_alexPatternParser

}

