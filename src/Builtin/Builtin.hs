module Builtin.Builtin where
     -- ( defaultBuiltins
     -- ) where

import Typing.Types
import Builtin.Types
import Parser.AST 
    ( Identifier(..)
    , Loc(..)
    , MultiplicityAtom(..)
    , TypeExpr(..)
    , ArrowExpr(..)
    , MultiplicityExpr(..)
    )
import Parser.Parser (parseType)

import qualified Data.HashMap.Strict as M
import qualified Data.HashSet as S
import Data.Bifunctor (bimap, first, second)

import Control.Monad.State

type BuiltinFunction = (Identifier, TypeScheme)

defaultBuiltins :: StaticContext
defaultBuiltins = StaticContext functions constructors types

functions :: M.HashMap Identifier TypeScheme
functions = M.fromList
    [ funcEquals
    , funcNotEquals
    , funcGreaterThan
    , funcLessThan
    , funcGreaterEqual
    , funcLessEqual
    , funcAdd
    , funcSub
    , funcMul
    , funcDiv
    , funcUndefined
    ]

constructors :: M.HashMap Identifier TypeScheme
constructors = M.fromList
    [ consTrue
    , consFalse
    , consListNil
    , consListCons
    ]

types :: S.HashSet Identifier
types = S.empty

funcEquals, funcNotEquals, funcGreaterThan, funcLessThan, funcGreaterEqual, funcLessEqual,
    funcAdd, funcSub, funcMul, funcDiv, funcUndefined :: BuiltinFunction
funcEquals       = (I "==", makeScheme "a -o a -o Bool")
funcNotEquals    = (I "!=", makeScheme "a -o a -o Bool")
funcGreaterThan  = (I ">", makeScheme "a -o a -o Bool")
funcLessThan     = (I "<", makeScheme "a -o a -o Bool")
funcGreaterEqual = (I ">=", makeScheme "a -o a -o Bool")
funcLessEqual    = (I "<=", makeScheme "a -o a -o Bool")
funcAdd          = (I "+", makeScheme "Int -o Int -o Int")
funcSub          = (I "-", makeScheme "Int -o Int -o Int")
funcMul          = (I "*", makeScheme "Int -o Int -o Int")
funcDiv          = (I "/", makeScheme "Int -o Int -o Int")
funcUndefined    = (I "undefined", makeScheme "a")

consTrue, consFalse, consListNil, consListCons :: BuiltinFunction
consTrue = (I "True", makeScheme "Bool")
consFalse = (I "False", makeScheme "Bool")
consListNil = (I "[]", makeScheme "[a]")
consListCons = (I "::", makeScheme "a -o [a] -o [a]")

type TypeBuilder a = State ( (Integer, M.HashMap Identifier Integer)
                           , (Integer, M.HashMap Identifier Integer)
                           ) a

makeScheme :: String -> TypeScheme
makeScheme typeString = case parseType typeString of
                          Right tExpr -> 
                              let startState = ((0, M.empty), (0, M.empty))
                                  (t, ((tvars, _), (mvars, _))) = runState (buildTypeFor tExpr) startState
                               in TypeScheme (S.fromList [0..(tvars-1)]) (S.fromList [0..(mvars-1)]) t
    where
        buildTypeFor :: Loc TypeExpr -> TypeBuilder Type
        buildTypeFor (L _ (TEGround name)) = pure (Ground name)
        buildTypeFor (L _ (TEPoly name)) = do
            nameMap <- gets (snd . fst)
            case M.lookup name nameMap of
              Just id -> pure (Poly id)
              Nothing -> do
                  id <- gets (fst . fst)
                  modify (first (bimap (+1) (M.insert name id)))
                  pure (Poly id)
        buildTypeFor (L _ (TEApp fun arg)) = do
            TypeApp <$> buildTypeFor fun <*> buildTypeFor arg
        buildTypeFor (L _ (TEArrow from mul to)) = do
            FunctionType <$> buildTypeFor from <*> buildArrowFor mul <*> buildTypeFor to
        buildTypeFor (L _ TEUnit) = pure unitType
        buildTypeFor (L _ (TETuple ts)) = TupleType <$> mapM buildTypeFor ts
        buildTypeFor (L _ (TEList t)) = TypeApp listTypeCon <$> buildTypeFor t

        buildArrowFor :: Loc ArrowExpr -> TypeBuilder Arrow
        buildArrowFor (L _ (ArrowExpr Nothing)) = pure (Arrow (MAtom Normal))
        buildArrowFor (L _ (ArrowExpr (Just (L _ m)))) = Arrow <$> buildMulFor m

        buildMulFor :: MultiplicityExpr -> TypeBuilder Multiplicity
        buildMulFor (MEPoly name) = do
            nameMap <- gets (snd . snd)
            case M.lookup name nameMap of
              Just id -> pure (MPoly id)
              Nothing -> do
                  id <- gets (fst . snd)
                  modify (second (bimap (+1) (M.insert name id)))
                  pure (MPoly id)
        buildMulFor (MEAtom atom) = pure (MAtom atom)
        buildMulFor (MEProd lhs rhs) = MProd <$> buildMulFor lhs <*> buildMulFor rhs


