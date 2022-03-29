module Preprocessor.Preprocessor where

import Parser.AST
import Typing.Types

import Control.Monad.Except
import Control.Monad.State
import qualified Data.HashMap.Strict as M

data PreprocessorError
    = NoMatchingImplementation

type Preprocessor a = ExceptT PreprocessorError (State StaticContext) a

transformAST :: [Loc Statement] -> StaticContext -> Preprocessor (Loc ValExpr)
transformAST stmts ctx = undefined
    where
        transform' :: [Loc Statement] -> Preprocessor [Loc LetBinding]
        transform' [] = pure []
        transform' (tLoc@(L _ (TypeDecl name t)) : fLoc@(L _ (FuncDecl name' body)) : rest)
            | syntax name == syntax name' = do
                let func = loc (embellishFunction name t body) tLoc fLoc
                (func:) <$> transform' rest

        embellishFunction :: Loc Identifier -> Loc TypeExpr -> Loc ValExpr -> LetBinding
        embellishFunction name@(L nameLoc _) tExpr@(L tLoc t) (L vLoc v) =
            let mul = Just (L nameLoc (MEAtom Normal))
                bindName = L nameLoc (Annotated (fmap VarPattern name) (Just tExpr))
                body = embellishLambdas t v
             in LetBinding mul bindName undefined
            where
                embe


