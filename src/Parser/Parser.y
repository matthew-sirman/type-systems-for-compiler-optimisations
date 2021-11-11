{
{-# LANGUAGE OverlappingInstances #-}
module Parser.Parser 
    ( parse
    , Statement(..)
    , ValExpr(..)
    , Literal(..)
    , TypeExpr(..)
    , Annotated(..)
    , CaseBranch(..)
    , Pattern(..)
    , ArrowType(..)
    , Multiplicity(..)
    , MultiplicityAtom(..)
    , Parser.Lexer.Identifier(..)

    , test_parseStmt
    , test_parseExpr
    , test_parseDatatype
    , test_parseType
    , test_parsePattern
    ) where

import Parser.Lexer

import qualified Data.List.NonEmpty as NE
import Data.List (intersperse)
}

%name alexParser program

%name test_alexStmtParser stmt
%name test_alexExprParser expr
%name test_alexTypeParser type
%name test_alexDatatypeParser datatype
%name test_alexPatternParser pattern

%tokentype { Token }
%error { parseError }
%monad { Alex }
%lexer { lexer } { TokEOF }
%expect 6

%token
    let                 { KWlet }
    in                  { KWin }
    case                { KWcase }
    of                  { KWof }
    if                  { KWif }
    then                { KWthen }
    else                { KWelse }
    data                { KWdata }
    where               { KWwhere }

    '='                 { TokEq }
    '=='                { TokEqEq }
    '!='                { TokNeq }
    '<'                 { TokLessThan }
    '>'                 { TokGreaterThan }
    '<='                { TokLessEq }
    '>='                { TokGreaterEq }
    '+'                 { TokPlus }
    '-'                 { TokMinus }
    '*'                 { TokTimes }
    '/'                 { TokDivide }

    '('                 { TokOpenParen }
    ')'                 { TokCloseParen }
    '['                 { TokOpenBracket }
    ']'                 { TokCloseBracket }
    ':'                 { TokColon }
    '->'                { TokArrow }
    '?'                 { TokQuestion }
    '!'                 { TokOne }
    '-o'                { TokLinearArrow }
    '-+'                { TokRelevantArrow }
    '-c'                { TokAffineArrow }

    '::'                { TokCons }

    ','                 { TokComma }
    '|'                 { TokPipe }
    '\\'                { TokBackslash }

    lvar                { TokLowerId $$ }
    uvar                { TokUpperId $$ }
    mvar                { TokMultiplicityId $$ }
    int                 { TokIntegerLit $$ }
    real                { TokRealLit $$ }

    ';;'                { TokEndStmt }

%right in '::'
%nonassoc '<' '>' '<=' '>=' '==' '!='
%left '+' '-'
%left '*' '/'
%left NEGATE

%%

program :: { [Statement] }
    : stmts                                             { reverse $1 }

stmts :: { [Statement] }
    : {- empty -}                                       { [] }
    | stmts stmt                                        { $2 : $1 }

stmt :: { Statement }
    : lvar ':' type ';;'                                { TypeDecl $1 $3 }
    | lvar '=' expr ';;'                                { FuncDecl $1 $3 }
    | lvar pattern_list '=' expr ';;'                   { makeFuncDecl $1 $2 $4 }
    | datatype ';;'                                     { TypeDef $1 }

expr :: { ValExpr Identifier }
    : let maybe(multiplicity) annotated(pattern) '=' expr in expr  { VELet $2 $3 $5 $7 }
    | case maybe(multiplicity) expr of case_branches    { VECase $2 $3 (NE.reverse $5) }
    | if maybe(multiplicity) expr then expr else expr   { makeIfCase $2 $3 $5 $7 }
    | '\\' annotated(pattern) arrow expr                { VELambda $2 $3 $4 }
    | term                                              { $1 }

term :: { ValExpr Identifier }
    : term '==' term                                    { VEApp (VEApp (VEVar "==") $1) $3 }
    | term '!=' term                                    { VEApp (VEApp (VEVar "!=") $1) $3 }
    | term '<' term                                     { VEApp (VEApp (VEVar "<") $1) $3 }
    | term '>' term                                     { VEApp (VEApp (VEVar ">") $1) $3 }
    | term '<=' term                                    { VEApp (VEApp (VEVar "<=") $1) $3 }
    | term '>=' term                                    { VEApp (VEApp (VEVar ">=") $1) $3 }
    | term '+' term                                     { VEApp (VEApp (VEVar "+") $1) $3 }
    | term '-' term                                     { VEApp (VEApp (VEVar "-") $1) $3 }
    | term '*' term                                     { VEApp (VEApp (VEVar "*") $1) $3 }
    | term '/' term                                     { VEApp (VEApp (VEVar "/") $1) $3 }
    | term '::' term                                    { VEApp (VEApp (VEVar "::") $1) $3 }
    | apps                                              { $1 }

apps :: { ValExpr Identifier }
    : apps atom                                         { VEApp $1 $2 }
    | atom                                              { $1 }

atom :: { ValExpr Identifier }
    : '(' expr ')'                                      { $2 }
    | lvar                                              { VEVar $1 }
    | uvar                                              { VEVar $1 }
    | int                                               { VELiteral (IntLiteral $1) }
    | real                                              { VELiteral (RealLiteral $1) }
    | tuple(expr)                                       { VELiteral (TupleLiteral $1) }
    | list(expr)                                        { VELiteral (ListLiteral $1) }

datatype :: { TypeDefinition }
    : data uvar seq(lvar) seq(mvar)                     { TypeDefinition $2 $3 $4 [] }
    | data uvar seq(lvar) seq(mvar) where constructors  { TypeDefinition $2 $3 $4 $6 }

constructors :: { [Annotated Identifier Identifier] }
    : constructor seq(constructor)                      { $1 : $2 }

constructor :: { Annotated Identifier Identifier }
    : '|' uvar ':' type                                 { Annotated $2 (Just $4) }

list(p)
    : '[' list_list(p) ']'                              { reverse $2 }

list_list(p)
    : {- empty -}                                       { [] }
    | p                                                 { [$1] }
    | list_list(p) ',' p                                { $3 : $1 }

seq(p)
    : seq_list(p)                                       { reverse $1 }

seq_list(p)
    : {- empty -}                                       { [] }
    | seq_list(p) p                                     { $2 : $1 }

annotated(p)
    : p                                                 { Annotated $1 Nothing }
    | p ':' type                                        { Annotated $1 (Just $3) }
    | '(' annotated(p) ')'                              { $2 }

case_branches :: { NE.NonEmpty (CaseBranch Identifier) }
    : case_branch                                       { $1 NE.:| [] }
    | case_branches case_branch                         { $2 NE.<| $1 }

case_branch :: { CaseBranch Identifier }
    : '|' pattern '->' expr                             { CaseBranch $2 $4 }

pattern_list :: { [Pattern] }
    : pattern                                           { [$1] }
    | pattern pattern_list                              { $1 : $2 }

pattern :: { Pattern }
    : uvar                                              { ConsPattern $1 [] }
    | '(' uvar pattern_list ')'                         { ConsPattern $2 $3 }
    | pattern_atom                                      { $1 }

pattern_atom :: { Pattern }
    : int                                               { LitPattern (IntLiteral $1) }
    | real                                              { LitPattern (RealLiteral $1) }
    | tuple(pattern)                                    { LitPattern (TupleLiteral $1) }
    | lvar                                              { VarPattern $1 }
    | '(' pattern ')'                                   { $2 }

type :: { TypeExpr Identifier }
    : type_apps arrow type                              { TEArrow $1 $2 $3 }
    | type_apps                                         { $1 }

type_apps :: { TypeExpr Identifier }
    : type_apps type_atom                               { TEApp $1 $2 }
    | type_atom                                         { $1 }

type_atom :: { TypeExpr Identifier }
    : uvar                                              { TEGround $1 }
    | lvar                                              { TEPoly $1 }
    | '(' ')'                                           { TEUnit }
    | tuple(type)                                       { TETuple $1 }
    | '[' type ']'                                      { TEList $2 }
    | '(' type ')'                                      { $2 }

tuple(p)
    : '(' tuple_list(p) ')'                             { (reverse $2) }

tuple_list(p)
    : p ',' p                                           { [$3, $1] }
    | tuple_list(p) ',' p                               { $3 : $1 }

arrow :: { ArrowType }
    : '->'                                              { Arrow (Just (MAtom Normal)) }
    | '-o'                                              { Arrow (Just (MAtom Linear)) }
    | '-+'                                              { Arrow (Just (MAtom Relevant)) }
    | '-c'                                              { Arrow (Just (MAtom Affine)) }
    | '->' multiplicity                                 { Arrow (Just $2) }

multiplicity :: { Multiplicity }
    : mvar                                              { MPoly $1 }
    | '*'                                               { MAtom Normal }
    | '!'                                               { MAtom Linear }
    | '+'                                               { MAtom Relevant }
    | '?'                                               { MAtom Affine }

maybe(p)
    : {- empty -}                                       { Nothing }
    | p                                                 { Just $1 }

{

data Statement
    = TypeDecl Identifier (TypeExpr Identifier)
    | FuncDecl Identifier (ValExpr Identifier)
    | TypeDef TypeDefinition
    deriving (Eq)

instance Show Statement where
    show (TypeDecl name t) = name ++ " : " ++ show t
    show (FuncDecl name body) = name ++ " = " ++ show body
    show (TypeDef def) = show def

data ValExpr poly
    = VELet (Maybe Multiplicity) (Annotated Pattern poly) (ValExpr poly) (ValExpr poly)
    | VECase (Maybe Multiplicity) (ValExpr poly) (NE.NonEmpty (CaseBranch poly))
    | VEApp (ValExpr poly) (ValExpr poly)
    | VELambda (Annotated Pattern poly) ArrowType (ValExpr poly)
    | VEVar Identifier
    | VELiteral (Literal (ValExpr poly))
    deriving (Eq)

instance Show poly => Show (ValExpr poly) where
    show (VELet m pattern bound body) = "let " ++ showMul m ++ " " ++ show pattern ++ " = " ++ show bound ++ " in " ++ show body
        where
            showMul Nothing = ""
            showMul (Just mul) = show mul
    show (VECase m disc branches) = "case " ++ showMul m ++ " " ++ show disc ++ " of " ++ (foldMap (('\n' :) . show) branches)
        where
            showMul Nothing = ""
            showMul (Just mul) = show mul
    show (VEApp fun arg) = case (fParen fun, aParen arg) of
                             (False, False) -> show fun ++ " " ++ show arg
                             (False, True) -> show fun ++ " (" ++ show arg ++ ")"
                             (True, False) -> "(" ++ show fun ++ ") " ++ show arg
                             (True, True) -> "(" ++ show fun ++ ") (" ++ show arg ++ ")"
        where
            fParen, aParen :: ValExpr poly -> Bool
            fParen (VEVar _) = False
            fParen (VEApp _ _) = False
            fParen _ = True

            aParen (VEVar _) = False
            aParen (VELiteral _) = False
            aParen _ = True
    show (VELambda pattern arrow body) = "\\" ++ show pattern ++ " " ++ show arrow ++ " " ++ show body
    show (VEVar name) = name
    show (VELiteral lit) = show lit

instance Functor ValExpr where
    fmap f (VELet m pattern bound body) = VELet m (fmap f pattern) (fmap f bound) (fmap f body)
    fmap f (VECase m disc bs) = VECase m (fmap f disc) (fmap (fmap f) bs)
    fmap f (VEApp fun arg) = VEApp (fmap f fun) (fmap f arg)
    fmap f (VELambda pattern arrow body) = VELambda (fmap f pattern) arrow (fmap f body)
    fmap _ (VEVar v) = VEVar v
    fmap f (VELiteral lit) = VELiteral (fmap (fmap f) lit)

instance Foldable ValExpr where
    foldMap f (VELet _ pattern bound body) = foldMap f pattern <> foldMap f bound <> foldMap f body
    foldMap f (VECase _ disc bs) = foldMap f disc <> foldMap (foldMap f) bs
    foldMap f (VEApp fun arg) = foldMap f fun <> foldMap f arg
    foldMap f (VELambda pattern _ body) = foldMap f pattern <> foldMap f body
    foldMap _ (VEVar _) = mempty
    foldMap f (VELiteral lit) = foldMap (foldMap f) lit

instance Traversable ValExpr where
    traverse f (VELet m pattern bound body) = VELet m <$> traverse f pattern <*> traverse f bound <*> traverse f body
    traverse f (VECase m disc bs) = VECase m <$> traverse f disc <*> traverse (traverse f) bs
    traverse f (VEApp fun arg) = VEApp <$> traverse f fun <*> traverse f arg
    traverse f (VELambda pattern arrow body) = VELambda <$> traverse f pattern <*> pure arrow <*> traverse f body
    traverse _ (VEVar v) = pure (VEVar v)
    traverse f (VELiteral lit) = VELiteral <$> traverse (traverse f) lit

data TypeDefinition
    = TypeDefinition Identifier [Identifier] [Identifier] [Annotated Identifier Identifier]
    deriving (Eq)

instance Show TypeDefinition where
    show (TypeDefinition name pArgs mArgs cases) =
        "data " ++ name ++ (concatMap (' ' :) pArgs) ++ (concatMap (' ' :) mArgs) ++ showCases cases
        where
            showCases :: [Annotated Identifier Identifier] -> String
            showCases [] = ""
            showCases cs = " where" ++ concatMap (("\n| " ++) . show) cs

data Literal a
    = IntLiteral Integer
    | RealLiteral Double
    | ListLiteral [a]
    | TupleLiteral [a]
    deriving (Eq)

instance Show a => Show (Literal a) where
    show (IntLiteral i) = show i
    show (RealLiteral r) = show r
    show (ListLiteral ls) = show ls
    show (TupleLiteral ts) = "(" ++ concat (intersperse ", " (map show ts)) ++ ")"

instance Functor Literal where
    fmap _ (IntLiteral i) = IntLiteral i
    fmap _ (RealLiteral r) = RealLiteral r
    fmap f (ListLiteral ls) = ListLiteral (fmap f ls)
    fmap f (TupleLiteral ts) = TupleLiteral (fmap f ts)

instance Foldable Literal where
    foldMap _ (IntLiteral _) = mempty
    foldMap _ (RealLiteral _) = mempty
    foldMap f (ListLiteral ls) = foldMap f ls
    foldMap f (TupleLiteral ts) = foldMap f ts

instance Traversable Literal where
    traverse _ (IntLiteral i) = pure (IntLiteral i)
    traverse _ (RealLiteral r) = pure (RealLiteral r)
    traverse f (ListLiteral ls) = ListLiteral <$> traverse f ls
    traverse f (TupleLiteral ts) = TupleLiteral <$> traverse f ts
    
data TypeExpr poly
    = TEGround Identifier
    | TEPoly poly
    | TEApp (TypeExpr poly) (TypeExpr poly)
    | TEArrow (TypeExpr poly) ArrowType (TypeExpr poly)
    | TEUnit 
    | TETuple [TypeExpr poly]
    | TEList (TypeExpr poly)
    deriving (Eq)

instance Show poly => Show (TypeExpr poly) where
    show (TEGround name) = name
    show (TEPoly p) = show p
    show (TEApp con arg) = case (cParen con, aParen arg) of
                             (False, False) -> show con ++ " " ++ show arg
                             (False, True) -> show con ++ " (" ++ show arg ++ ")"
                             (True, False) -> "(" ++ show con ++ ") " ++ show arg
                             (True, True) -> "(" ++ show con ++ ") (" ++ show arg ++ ")"
        where
            cParen, aParen :: TypeExpr poly -> Bool
            cParen (TEGround _) = False
            cParen (TEPoly _) = False
            cParen (TEApp _ _) = False
            cParen _ = True

            aParen (TEGround _) = False
            aParen TEUnit = False
            aParen (TETuple _) = False
            aParen (TEList _) = False
            aParen _ = True
    show (TEArrow from@(TEArrow _ _ _) arrow to) = "(" ++ show from ++ ") " ++ show arrow ++ " " ++ show to
    show (TEArrow from arrow to) = show from ++ " " ++ show arrow ++ " " ++ show to
    show TEUnit = "()"
    show (TETuple ts) = "(" ++ concat (intersperse ", " (map show ts)) ++ ")"
    show (TEList t) = "[" ++ show t ++ "]"

instance Functor TypeExpr where
    fmap _ (TEGround name) = TEGround name
    fmap f (TEPoly p) = TEPoly (f p)
    fmap f (TEApp con arg) = TEApp (fmap f con) (fmap f arg)
    fmap f (TEArrow from arrow to) = TEArrow (fmap f from) arrow (fmap f to)
    fmap _ TEUnit = TEUnit
    fmap f (TETuple ts) = TETuple (fmap (fmap f) ts)
    fmap f (TEList t) = TEList (fmap f t)

instance Foldable TypeExpr where
    foldMap _ (TEGround _) = mempty
    foldMap f (TEPoly p) = f p
    foldMap f (TEApp con arg) = foldMap f con <> foldMap f arg
    foldMap f (TEArrow from _ to) = foldMap f from <> foldMap f to
    foldMap _ TEUnit = mempty
    foldMap f (TETuple ts) = foldMap (foldMap f) ts
    foldMap f (TEList t) = foldMap f t

instance Traversable TypeExpr where
    traverse _ (TEGround name) = pure (TEGround name)
    traverse f (TEPoly p) = TEPoly <$> f p
    traverse f (TEApp con arg) = TEApp <$> traverse f con <*> traverse f arg
    traverse f (TEArrow from arrow to) = TEArrow <$> traverse f from <*> pure arrow <*> traverse f to
    traverse _ TEUnit = pure TEUnit
    traverse f (TETuple ts) = TETuple <$> traverse (traverse f) ts
    traverse f (TEList t) = TEList <$> traverse f t

data Annotated a poly = Annotated a (Maybe (TypeExpr poly))
    deriving (Eq)

instance Show poly => Show (Annotated Identifier poly) where
    show (Annotated name (Just t)) = "(" ++ name ++ " : " ++ show t ++ ")"
    show (Annotated name Nothing) = name

instance (Show a, Show poly) => Show (Annotated a poly) where
    show (Annotated x (Just t)) = "(" ++ show x ++ " : " ++ show t ++ ")"
    show (Annotated x Nothing) = show x

instance Functor (Annotated a) where
    fmap f (Annotated val t) = Annotated val (fmap (fmap f) t)

instance Foldable (Annotated a) where
    foldMap f (Annotated _ t) = foldMap (foldMap f) t

instance Traversable (Annotated a) where
    traverse f (Annotated val t) = Annotated val <$> (traverse (traverse f) t)

data CaseBranch poly = CaseBranch Pattern (ValExpr poly)
    deriving (Eq)

instance Show poly => Show (CaseBranch poly) where
    show (CaseBranch pattern expr) = "| " ++ show pattern ++ " -> " ++ show expr

instance Functor CaseBranch where
    fmap f (CaseBranch pattern expr) = CaseBranch pattern (fmap f expr)

instance Foldable CaseBranch where
    foldMap f (CaseBranch _ expr) = foldMap f expr

instance Traversable CaseBranch where
    traverse f (CaseBranch pattern expr) = CaseBranch pattern <$> traverse f expr

data Pattern
    = VarPattern Identifier
    | ConsPattern Identifier [Pattern]
    | LitPattern (Literal Pattern)
    deriving (Eq)

instance Show Pattern where
    show (VarPattern name) = name
    show (ConsPattern name []) = name
    show (ConsPattern name args) = "(" ++ name ++ concatMap ((' ':) . show) args ++ ")"
    show (LitPattern lit) = show lit

data ArrowType = Arrow (Maybe Multiplicity)
    deriving (Eq)

instance Show ArrowType where
    show (Arrow Nothing) = "->"
    show (Arrow (Just (MAtom Normal))) = "->"
    show (Arrow (Just (MAtom Linear))) = "-o"
    show (Arrow (Just m)) = "-> " ++ show m

data Multiplicity
    = MPoly Identifier
    | MAtom MultiplicityAtom
    -- | MSub Multiplicity
    -- | MDiv Multiplicity Multiplicity
    -- | MZero
    deriving (Eq)

instance Show Multiplicity where
    show (MPoly name) = name
    show (MAtom atom) = show atom

data MultiplicityAtom
    = Normal
    | Linear
    | Relevant
    | Affine
    deriving (Eq)

instance Show MultiplicityAtom where
    show Normal = "*"
    show Linear = "!"
    show Relevant = "+"
    show Affine = "?"

makeFuncDecl :: Identifier -> [Pattern] -> ValExpr Identifier -> Statement
makeFuncDecl name patterns expr = FuncDecl name (transformLambdas patterns)
    where
        transformLambdas :: [Pattern] -> ValExpr Identifier
        transformLambdas [] = expr
        transformLambdas (p:ps) = VELambda (Annotated p Nothing) (Arrow Nothing) (transformLambdas ps)

makeIfCase :: Maybe Multiplicity -> ValExpr Identifier -> ValExpr Identifier -> ValExpr Identifier -> ValExpr Identifier
makeIfCase m cond ifT ifF = VECase m cond (thenBranch NE.:| [elseBranch])
    where
        thenBranch = CaseBranch (VarPattern "True") ifT
        elseBranch = CaseBranch (VarPattern "False") ifF

lexer :: (Token -> Alex a) -> Alex a
lexer cont = do
    tok <- alexMonadScan
    cont tok

parseError t = do
    ((AlexPn _ line column), a, b, c) <- alexGetInput
    alexError ("parser error at line " ++ (show line) ++ ", column " ++ (show column) ++ ". Unexpected token " ++ (show t) ++ ".")

parse :: String -> Either String [Statement]
parse s = runAlex s alexParser

test_parseStmt :: String -> Either String Statement
test_parseStmt s = runAlex s test_alexStmtParser

test_parseExpr :: String -> Either String (ValExpr Identifier)
test_parseExpr s = runAlex s test_alexExprParser

test_parseDatatype :: String -> Either String TypeDefinition
test_parseDatatype s = runAlex s test_alexDatatypeParser

test_parseType :: String -> Either String (TypeExpr Identifier)
test_parseType s = runAlex s test_alexTypeParser

test_parsePattern :: String -> Either String Pattern
test_parsePattern s = runAlex s test_alexPatternParser

}

