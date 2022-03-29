{-# LANGUAGE FlexibleInstances, DeriveGeneric #-}
module Parser.AST
    ( Statement(..)
    , ValExpr(..)
    , TypeDefinition(..)
    , LetBinding(..)
    , Literal(..)
    , TypeExpr(..)
    , Annotated(..)
    , CaseBranch(..)
    , SourcePattern(..)
    , ArrowExpr(..)
    , MultiplicityExpr(..)
    , MultiplicityAtom(..)
    , SourceLocation(..)
    , Loc(..)
    , loc

    , Identifier(..)
    ) where

import qualified Util.BoundedPoset as B

import Data.List (intercalate)
import qualified Data.List.NonEmpty as NE

import GHC.Generics (Generic)
import Data.Hashable (Hashable)

data SourceLocation = SL
    { slStart :: Int
    , slEnd :: Int
    , slLine :: Int
    }
    deriving (Eq, Generic)

instance Show SourceLocation where
    show loc = "<line: " ++ show (slLine loc) ++ ">: "

instance Hashable SourceLocation

data Loc a = L 
    { location :: SourceLocation 
    , syntax :: a
    }
    deriving (Eq, Generic)

instance Show a => Show (Loc a) where
    show = show . syntax

instance Functor Loc where
    fmap f (L sl x) = L sl (f x)

loc :: a -> Loc s -> Loc e -> Loc a
loc element (L start _) (L end _) = L (SL (slStart start) (slEnd end) (slLine start)) element

instance Hashable a => Hashable (Loc a)

----------------------------------
--        AST Data Types        --
----------------------------------

newtype Identifier = I String
    deriving (Eq, Ord, Generic)

instance Hashable Identifier

data Statement
    = TypeDecl (Loc Identifier) (Loc TypeExpr)
    | FuncDecl (Loc Identifier) (Loc ValExpr)
    | TypeDef (Loc TypeDefinition)
    deriving (Eq)

data ValExpr
    = VELet [Loc LetBinding] (Loc ValExpr)
    | VECase (Maybe (Loc MultiplicityExpr)) (Loc ValExpr) (NE.NonEmpty (Loc CaseBranch))
    | VEApp (Loc ValExpr) (Loc ValExpr)
    | VELambda (Loc (Annotated SourcePattern)) (Loc ArrowExpr) (Loc ValExpr)
    | VEVar Identifier
    | VELiteral (Literal (Loc ValExpr))
    deriving (Eq)

data TypeDefinition
    = TypeDefinition (Loc Identifier) [Loc Identifier] [Loc Identifier] [Loc (Annotated Identifier)]
    deriving (Eq)

data LetBinding = LetBinding (Maybe (Loc MultiplicityExpr)) (Loc (Annotated SourcePattern)) (Loc ValExpr)
    deriving (Eq)

data Literal a
    = IntLiteral Int
    | RealLiteral Double
    | ListLiteral [a]
    | TupleLiteral [a]
    deriving (Eq)

data TypeExpr
    = TEGround Identifier
    | TEPoly Identifier
    | TEApp  (Loc TypeExpr) (Loc TypeExpr)
    | TEArrow (Loc TypeExpr) (Loc ArrowExpr) (Loc TypeExpr)
    | TEUnit
    | TETuple [Loc TypeExpr]
    | TEList (Loc TypeExpr)
    deriving (Eq)

data Annotated a = Annotated (Loc a) (Maybe (Loc TypeExpr))
    deriving (Eq)

data CaseBranch = CaseBranch (Loc SourcePattern) (Loc ValExpr)
    deriving (Eq)

data SourcePattern
    = VarPattern Identifier
    | ConsPattern Identifier [Loc SourcePattern]
    | LitPattern (Literal (Loc SourcePattern))
    deriving (Eq)

newtype ArrowExpr = ArrowExpr (Maybe (Loc MultiplicityExpr))
    deriving (Eq)

data MultiplicityExpr
    = MEPoly Identifier
    | MEAtom MultiplicityAtom
    | MEProd MultiplicityExpr MultiplicityExpr
    deriving (Eq, Ord)

data MultiplicityAtom
    = Normal
    | Linear
    | Relevant
    | Affine
    deriving (Eq, Ord, Generic)

----------------------------------------
--        Identifier Instances        --
----------------------------------------

instance Show Identifier where
    show (I name) = name

---------------------------------------
--        Statement Instances        --
---------------------------------------

instance Show Statement where
    show (TypeDecl name t) = show name ++ " : " ++ show t
    show (FuncDecl name body) = show name ++ " = " ++ show body
    show (TypeDef def) = show def

-------------------------------------
--        ValExpr Instances        --
-------------------------------------

instance Show ValExpr where
    show (VELet bindings body) = "let " ++ intercalate " and " (map show bindings) ++ " in " ++ show body
    show (VECase Nothing disc branches) = "case " ++ show disc ++ " of " ++ foldMap (('\n' :) . show) branches
    show (VECase (Just m) disc branches) = "case " ++ show m ++ " " ++ show disc ++ " of " ++ foldMap (('\n' :) . show) branches
    show (VEApp fun arg) = funString fun ++ " " ++ argString arg
        where
            funString, argString :: Loc ValExpr -> String

            funString (L _ (VEVar {})) = show fun
            funString (L _ (VEApp {})) = show fun
            funString _ = "(" ++ show fun ++ ")"

            argString (L _ (VEVar {})) = show arg
            argString (L _ (VELiteral {})) = show arg
            argString _ = "(" ++ show arg ++ ")"
    show (VELambda pattern arrow body) = "\\" ++ show pattern ++ " " ++ show arrow ++ " " ++ show body
    show (VEVar name) = show name
    show (VELiteral lit) = show lit

--------------------------------------------
--        TypeDefinition Instances        --
--------------------------------------------

instance Show TypeDefinition where
    show (TypeDefinition name pArgs mArgs cases) =
        "data " ++ show name ++ concatMap ((' ' :) . show) pArgs ++ concatMap ((' ' :) . show) mArgs ++ showCases cases
        where
            showCases :: [Loc (Annotated Identifier)] -> String
            showCases [] = ""
            showCases cs = " where" ++ concatMap (("\n| " ++) . show) cs

----------------------------------------
--        LetBinding Instances        --
----------------------------------------

instance Show LetBinding where
    show (LetBinding m pattern expr) = showMul m ++ show pattern ++ " = " ++ show expr
        where
            showMul Nothing = ""
            showMul (Just mul) = show mul ++ " "

-------------------------------------
--        Literal Instances        --
-------------------------------------

instance Show a => Show (Literal a) where
    show (IntLiteral i) = show i
    show (RealLiteral r) = show r
    show (ListLiteral ls) = show ls
    show (TupleLiteral ts) = "(" ++ intercalate ", " (map show ts) ++ ")"

instance Functor Literal where
    fmap _ (IntLiteral i) = IntLiteral i
    fmap _ (RealLiteral r) = RealLiteral r
    fmap f (ListLiteral ls) = ListLiteral (fmap f ls)
    fmap f (TupleLiteral ts) = TupleLiteral (fmap f ts)

--------------------------------------
--        TypeExpr Instances        --
--------------------------------------

instance Show TypeExpr where
    show (TEGround name) = show name
    show (TEPoly p) = show p
    show (TEApp con arg) = conString con ++ " " ++ argString arg
        where
            conString, argString :: Loc TypeExpr -> String

            conString (L _ (TEGround {})) = show con
            conString (L _ (TEPoly {})) = show con
            conString (L _ (TEApp {})) = show con
            conString _ = "(" ++ show con ++ ")"

            argString (L _ (TEGround {})) = show arg
            argString (L _ (TEUnit {})) = show arg
            argString (L _ (TETuple {})) = show arg
            argString (L _ (TEList {})) = show arg
            argString _ = "(" ++ show arg ++ ")"
    show (TEArrow from@(L _ (TEArrow {})) arrow to) = "(" ++ show from ++ ") " ++ show arrow ++ " " ++ show to
    show (TEArrow from arrow to) = show from ++ " " ++ show arrow ++ " " ++ show to
    show TEUnit = "()"
    show (TETuple ts) = "(" ++ intercalate ", " (map show ts) ++ ")"
    show (TEList t) = "[" ++ show t ++ "]"

---------------------------------------
--        Annotated Instances        --
---------------------------------------

instance Show a => Show (Annotated a) where
    show (Annotated x (Just t)) = "(" ++ show x ++ " : " ++ show t ++ ")"
    show (Annotated x Nothing) = show x

----------------------------------------
--        CaseBranch Instances        --
----------------------------------------

instance Show CaseBranch where
    show (CaseBranch pattern expr) = "| " ++ show pattern ++ " -> " ++ show expr

-------------------------------------
--        Pattern Instances        --
-------------------------------------

instance Show SourcePattern where
    show (VarPattern name) = show name
    show (ConsPattern name []) = show name
    show (ConsPattern name args) = "(" ++ show name ++ concatMap ((' ':) . show) args ++ ")"
    show (LitPattern lit) = show lit

---------------------------------------
--        ArrowExpr Instances        --
---------------------------------------

instance Show ArrowExpr where
    show (ArrowExpr Nothing) = "->"
    show (ArrowExpr (Just (L _ (MEAtom Normal)))) = "->"
    show (ArrowExpr (Just (L _ (MEAtom Linear)))) = "-o"
    show (ArrowExpr (Just m)) = "-> " ++ show m

------------------------------------------
--        Multiplicity Instances        --
------------------------------------------

instance Show MultiplicityExpr where
    show (MEPoly name) = show name
    show (MEAtom atom) = show atom
    show (MEProd lhs rhs) = show lhs ++ " * " ++ show rhs

----------------------------------------------
--        MultiplicityAtom Instances        --
----------------------------------------------

instance Show MultiplicityAtom where
    show Normal = "*"
    show Linear = "!"
    show Relevant = "+"
    show Affine = "?"

instance Hashable MultiplicityAtom

