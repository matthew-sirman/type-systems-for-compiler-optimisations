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
    , Pattern(..)
    , ArrowExpr(..)
    , Multiplicity(..)
    , MultiplicityAtom(..)
    , SourceLocation(..)
    , Loc(..)

    , Identifier(..)
    ) where

import Data.List (intercalate)
import qualified Data.List.NonEmpty as NE

import GHC.Generics (Generic)
import Data.Hashable (Hashable)

data SourceLocation = SL
    { slStart :: Int
    , slEnd :: Int
    , slLine :: Int
    }
    deriving (Eq)

instance Show SourceLocation where
    show loc = "<line: " ++ show (slLine loc) ++ ">: "

data Loc a = L 
    { location :: SourceLocation 
    , syntax :: a
    }
    deriving Eq

instance Show a => Show (Loc a) where
    show = show . syntax

instance Functor Loc where
    fmap f (L sl x) = L sl (f x)

----------------------------------
--        AST Data Types        --
----------------------------------

newtype Identifier = I String
    deriving (Eq, Generic)

instance Hashable Identifier

data Statement
    = TypeDecl (Loc Identifier) (Loc TypeExpr)
    | FuncDecl (Loc Identifier) (Loc ValExpr)
    | TypeDef (Loc TypeDefinition)
    deriving (Eq)

data ValExpr
    = VELet [Loc LetBinding] (Loc ValExpr)
    | VECase (Maybe (Loc Multiplicity)) (Loc ValExpr) (NE.NonEmpty (Loc CaseBranch))
    | VEApp (Loc ValExpr) (Loc ValExpr)
    | VELambda (Loc (Annotated Pattern)) (Loc ArrowExpr) (Loc ValExpr)
    | VEVar Identifier
    | VELiteral (Literal (Loc ValExpr))
    deriving (Eq)

data TypeDefinition
    = TypeDefinition (Loc Identifier) [Loc Identifier] [Loc Identifier] [Loc (Annotated Identifier)]
    deriving (Eq)

data LetBinding = LetBinding (Maybe (Loc Multiplicity)) (Loc (Annotated Pattern)) (Loc ValExpr)
    deriving (Eq)

data Literal a
    = IntLiteral Integer
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

data CaseBranch = CaseBranch (Loc Pattern) (Loc ValExpr)
    deriving (Eq)

data Pattern
    = VarPattern Identifier
    | ConsPattern Identifier [Loc Pattern]
    | LitPattern (Literal (Loc Pattern))
    deriving (Eq)

newtype ArrowExpr = ArrowExpr (Maybe (Loc Multiplicity))
    deriving (Eq)

data Multiplicity
    = MPoly Identifier
    | MAtom MultiplicityAtom
    -- | MSub Multiplicity
    -- | MDiv Multiplicity Multiplicity
    -- | MZero
    deriving (Eq)

data MultiplicityAtom
    = Normal
    | Linear
    | Relevant
    | Affine
    deriving (Eq)


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

instance Show Pattern where
    show (VarPattern name) = show name
    show (ConsPattern name []) = show name
    show (ConsPattern name args) = "(" ++ show name ++ concatMap ((' ':) . show) args ++ ")"
    show (LitPattern lit) = show lit

---------------------------------------
--        ArrowExpr Instances        --
---------------------------------------

instance Show ArrowExpr where
    show (ArrowExpr Nothing) = "->"
    show (ArrowExpr (Just (L _ (MAtom Normal)))) = "->"
    show (ArrowExpr (Just (L _ (MAtom Linear)))) = "-o"
    show (ArrowExpr (Just m)) = "-> " ++ show m

------------------------------------------
--        Multiplicity Instances        --
------------------------------------------

instance Show Multiplicity where
    show (MPoly name) = show name
    show (MAtom atom) = show atom

----------------------------------------------
--        MultiplicityAtom Instances        --
----------------------------------------------

instance Show MultiplicityAtom where
    show Normal = "*"
    show Linear = "!"
    show Relevant = "+"
    show Affine = "?"
