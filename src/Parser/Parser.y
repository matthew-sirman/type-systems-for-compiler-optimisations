{
{-# LANGUAGE OverlappingInstances #-}
module Parser.Parser 
    ( parse
    , Statement(..)
    , ValExpr(..)
    , TypeDefinition(..)
    , LetBinding(..)
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
%expect 40

%token
    let                 { KWlet }
    and                 { KWand }
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
    | SL LN lvar pattern_list '=' expr SL ';;'          { makeFuncDecl (SL $1 $7 $2) $3 $4 $6 }
    | datatype ';;'                                     { TypeDef $1 }

expr :: { ValExpr Identifier }
    : SL LN let let_binding_list in expr SL             { VELet (SL $1 $7 $2) (reverse $4) $6 }
    | SL LN case maybe(multiplicity) expr of case_branches SL { VECase (SL $1 $8 $2) $4 $5 (NE.reverse $7) }
    | SL LN if maybe(multiplicity) expr then expr else expr SL { makeIfCase (SL $1 $10 $2) $4 $5 $7 $9 }
    | SL LN '\\' annotated(pattern) arrow expr SL       { VELambda (SL $1 $7 $2) $4 $5 $6 }
    | term                                              { $1 }

term :: { ValExpr Identifier }
    : SL LN term SL LN binop SL LN term SL              { VEApp (SL $7 $10 $8) (VEApp (SL $1 $4 $2) (VEVar (SL $4 $7 $5) $6) $3) $9 }
    | apps                                              { $1 }

apps :: { ValExpr Identifier }
    : SL LN apps atom SL                                { VEApp (SL $1 $5 $2) $3 $4 }
    | atom                                              { $1 }

atom :: { ValExpr Identifier }
    : '(' expr ')'                                      { $2 }
    | SL LN lvar SL                                     { VEVar (SL $1 $4 $2) $3 }
    | SL LN uvar SL                                     { VEVar (SL $1 $4 $2) $3 }
    | SL LN int SL                                      { VELiteral (SL $1 $4 $2) (IntLiteral $3) }
    | SL LN real SL                                     { VELiteral (SL $1 $4 $2) (RealLiteral $3) }
    | SL LN tuple(expr) SL                              { VELiteral (SL $1 $4 $2) (TupleLiteral $3) }
    | SL LN list(expr) SL                               { VELiteral (SL $1 $4 $2) (ListLiteral $3) }

binop :: { String }
    : '=='                                              { "==" }
    | '!='                                              { "!=" }
    | '<'                                               { "<" }
    | '>'                                               { ">" }
    | '<='                                              { "<=" }
    | '>='                                              { ">=" }
    | '+'                                               { "+" }
    | '-'                                               { "-" }
    | '*'                                               { "*" }
    | '/'                                               { "/" }
    | '::'                                              { "::" }

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

let_binding_list :: { [LetBinding Identifier] }
    : let_binding                                       { [$1] }
    | let_binding_list and let_binding                  { $3 : $1 }

let_binding :: { LetBinding Identifier }
    : maybe(multiplicity) annotated(pattern) '=' expr   { LetBinding $1 $2 $4 }

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
    | list(pattern)                                     { LitPattern (ListLiteral $1) }
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

SL :: { Int }
    : {- empty -}                                       {% getSourceLocation }

LN :: { Int }
    : {- empty -}                                       {% getLineNumber }

{

data SourceLocation = SL
    { slStart :: Int
    , slEnd :: Int
    , slLine :: Int
    }
    deriving (Eq)

data Statement
    = TypeDecl Identifier (TypeExpr Identifier)
    | FuncDecl Identifier (ValExpr Identifier)
    | TypeDef TypeDefinition
    deriving (Eq)

instance Show Statement where
    show (TypeDecl name t) = name ++ " : " ++ show t
    show (FuncDecl name body) = name ++ " = " ++ show body
    show (TypeDef def) = show def

-- TODO: Maybe make ValExpr a bifunctor in the identifier name and polymorphic type?
-- TODO: Add source location tags to each constructor for better error messages
data ValExpr poly
    = VELet SourceLocation [LetBinding poly] (ValExpr poly)
    | VECase SourceLocation (Maybe Multiplicity) (ValExpr poly) (NE.NonEmpty (CaseBranch poly))
    | VEApp SourceLocation (ValExpr poly) (ValExpr poly)
    | VELambda SourceLocation (Annotated Pattern poly) ArrowType (ValExpr poly)
    | VEVar SourceLocation Identifier
    | VELiteral SourceLocation (Literal (ValExpr poly))
    deriving (Eq)

instance Show poly => Show (ValExpr poly) where
    show (VELet _ bindings body) = "let " ++ concat (intersperse " and " (map show bindings)) ++ " in " ++ show body
    show (VECase _ m disc branches) = "case " ++ showMul m ++ " " ++ show disc ++ " of " ++ (foldMap (('\n' :) . show) branches)
        where
            showMul Nothing = ""
            showMul (Just mul) = show mul
    show (VEApp _ fun arg) = case (fParen fun, aParen arg) of
                             (False, False) -> show fun ++ " " ++ show arg
                             (False, True) -> show fun ++ " (" ++ show arg ++ ")"
                             (True, False) -> "(" ++ show fun ++ ") " ++ show arg
                             (True, True) -> "(" ++ show fun ++ ") (" ++ show arg ++ ")"
        where
            fParen, aParen :: ValExpr poly -> Bool
            fParen (VEVar _ _) = False
            fParen (VEApp _ _ _) = False
            fParen _ = True

            aParen (VEVar _ _) = False
            aParen (VELiteral _ _) = False
            aParen _ = True
    show (VELambda _ pattern arrow body) = "\\" ++ show pattern ++ " " ++ show arrow ++ " " ++ show body
    show (VEVar _ name) = name
    show (VELiteral _ lit) = show lit

instance Functor ValExpr where
    fmap f (VELet sl bindings body) = VELet sl (fmap (fmap f) bindings) (fmap f body)
    fmap f (VECase sl m disc bs) = VECase sl m (fmap f disc) (fmap (fmap f) bs)
    fmap f (VEApp sl fun arg) = VEApp sl (fmap f fun) (fmap f arg)
    fmap f (VELambda sl pattern arrow body) = VELambda sl (fmap f pattern) arrow (fmap f body)
    fmap _ (VEVar sl v) = VEVar sl v
    fmap f (VELiteral sl lit) = VELiteral sl (fmap (fmap f) lit)

instance Foldable ValExpr where
    foldMap f (VELet _ bindings body) = foldMap (foldMap f) bindings <> foldMap f body
    foldMap f (VECase _ _ disc bs) = foldMap f disc <> foldMap (foldMap f) bs
    foldMap f (VEApp _ fun arg) = foldMap f fun <> foldMap f arg
    foldMap f (VELambda _ pattern _ body) = foldMap f pattern <> foldMap f body
    foldMap _ (VEVar _ _) = mempty
    foldMap f (VELiteral _ lit) = foldMap (foldMap f) lit

instance Traversable ValExpr where
    traverse f (VELet sl bindings body) = VELet sl <$> traverse (traverse f) bindings <*> traverse f body
    traverse f (VECase sl m disc bs) = VECase sl m <$> traverse f disc <*> traverse (traverse f) bs
    traverse f (VEApp sl fun arg) = VEApp sl <$> traverse f fun <*> traverse f arg
    traverse f (VELambda sl pattern arrow body) = VELambda sl <$> traverse f pattern <*> pure arrow <*> traverse f body
    traverse _ (VEVar sl v) = pure (VEVar sl v)
    traverse f (VELiteral sl lit) = VELiteral sl <$> traverse (traverse f) lit

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

data LetBinding poly = LetBinding (Maybe Multiplicity) (Annotated Pattern poly) (ValExpr poly)
    deriving (Eq)

instance Show poly => Show (LetBinding poly) where
    show (LetBinding m pattern expr) = showMul m ++ show pattern ++ " = " ++ show expr
        where
            showMul Nothing = ""
            showMul (Just mul) = show mul ++ " "

instance Functor LetBinding where
    fmap f (LetBinding m pattern expr) = LetBinding m (fmap f pattern) (fmap f expr)

instance Foldable LetBinding where
    foldMap f (LetBinding _ pattern expr) = foldMap f pattern <> foldMap f expr

instance Traversable LetBinding where
    traverse f (LetBinding m pattern expr) = LetBinding m <$> traverse f pattern <*> traverse f expr

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

makeFuncDecl :: SourceLocation -> Identifier -> [Pattern] -> ValExpr Identifier -> Statement
makeFuncDecl sl name patterns expr = FuncDecl name (transformLambdas patterns)
    where
        transformLambdas :: [Pattern] -> ValExpr Identifier
        transformLambdas [] = expr
        transformLambdas (p:ps) = VELambda sl (Annotated p Nothing) (Arrow Nothing) (transformLambdas ps)

makeIfCase :: SourceLocation -> Maybe Multiplicity -> ValExpr Identifier -> ValExpr Identifier -> ValExpr Identifier -> ValExpr Identifier
makeIfCase sl m cond ifT ifF = VECase sl m cond (thenBranch NE.:| [elseBranch])
    where
        thenBranch = CaseBranch (VarPattern "True") ifT
        elseBranch = CaseBranch (VarPattern "False") ifF

lexer :: (Token -> Alex a) -> Alex a
lexer cont = do
    tok <- alexMonadScan
    cont tok

parseError :: Token -> Alex a
parseError t = do
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

