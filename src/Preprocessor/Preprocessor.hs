module Preprocessor.Preprocessor where

import Parser.AST
import Typing.Types
import Error.Error (showContext)

import Control.Monad.Except
import Control.Monad.State
import Control.Lens
import qualified Data.HashMap.Strict as M
import qualified Data.HashSet as S

data PreprocessorError
    = NoMatchingImplementation SourceLocation Identifier
    | TypeAnnotationMismatch SourceLocation TypeExpr TypeExpr
    | MulAnnotationMismatch SourceLocation MultiplicityExpr MultiplicityExpr

showPPError :: String -> PreprocessorError -> String
showPPError text (NoMatchingImplementation sl name) =
    showContext text sl ++ "No matching implementation for function \"" ++ show name ++ "\"."
showPPError text (TypeAnnotationMismatch sl ty ty') =
    showContext text sl ++ "Type annotation conflict between \"" ++ show ty ++ "\" and \"" ++ show ty' ++ "\"."
showPPError text (MulAnnotationMismatch sl m m') =
    showContext text sl ++ "Multiplicity annotation conflict between \"" ++ show m ++ "\" and \"" ++ show m' ++ "\"."

type Preprocessor a = ExceptT PreprocessorError (State StaticContext) a

transformAST :: [Loc Statement] -> StaticContext -> Either PreprocessorError (Loc ValExpr, StaticContext)
transformAST stmts ctx = 
    let (bindingsOrError, ctx') = runState (runExceptT (transform' stmts)) ctx
     in case bindingsOrError of
          Left err -> Left err
          Right bindings ->
              let xs = map (slEnd . location) bindings
                  endOfFile = maximum (map (slEnd . location) bindings)
                  wholeFileLoc = SL 0 endOfFile 1
               in Right (L wholeFileLoc (VELet bindings (L wholeFileLoc (VEVar (I "main")))), ctx')
    where
        transform' :: [Loc Statement] -> Preprocessor [Loc LetBinding]
        transform' [] = pure []
        transform' (tLoc@(L _ (TypeDecl name t)) : fLoc@(L _ (FuncDecl name' body)) : rest)
            | syntax name == syntax name' = do
                embellished <- embellishFunction name t body
                let func = loc embellished tLoc fLoc
                (func:) <$> transform' rest
        transform' (L _ (TypeDecl name _) : _) =
            throwError (NoMatchingImplementation (location name) (syntax name))
        transform' (fLoc@(L _ (FuncDecl name body)):rest) = do
            let mul = Just (L (location name) (MEAtom Normal))
                bindName = L (location name) (Annotated (fmap VarPattern name) Nothing)
                func = LetBinding mul bindName body <$ fLoc
            (func:) <$> transform' rest
        transform' (L _ (TypeDef (L _ def)):rest) = do
            addTypeDef def
            transform' rest

        embellishFunction :: Loc Identifier -> Loc TypeExpr -> Loc ValExpr -> Preprocessor LetBinding
        embellishFunction name tExpr vExpr = do
            let mul 
                    | syntax name == I "main" = Just (L (location name) (MEAtom Linear))
                    | otherwise = Just (L (location name) (MEAtom Normal))
                bindName = L (location name) (Annotated (fmap VarPattern name) (Just tExpr))
            body <- embellishLambdas tExpr vExpr
            pure (LetBinding mul bindName body)
            where
                embellishLambdas :: Loc TypeExpr -> Loc ValExpr -> Preprocessor (Loc ValExpr)
                embellishLambdas (L _ (TEArrow from mul to)) (L lamLoc (VELambda pat arrow body)) = do
                    let Annotated pattern patType = syntax pat
                    patType' <- unifyTypes from patType
                    mul' <- unifyMuls mul arrow
                    body' <- embellishLambdas to body
                    let pat' = Annotated pattern (Just patType') <$ pat
                    pure (L lamLoc (VELambda pat' mul' body'))
                embellishLambdas _ expr = pure expr

                unifyTypes :: Loc TypeExpr -> Maybe (Loc TypeExpr) -> Preprocessor (Loc TypeExpr)
                unifyTypes ty Nothing = pure ty
                unifyTypes ty (Just ty')
                    | syntax ty == syntax ty' = pure ty'
                    | otherwise = throwError (TypeAnnotationMismatch (location ty') (syntax ty) (syntax ty'))

                unifyMuls :: Loc ArrowExpr -> Loc ArrowExpr -> Preprocessor (Loc ArrowExpr)
                unifyMuls (L _ (ArrowExpr Nothing)) arrow@(L _ (ArrowExpr Nothing)) = pure arrow
                unifyMuls mul@(L _ (ArrowExpr (Just _))) (L _ (ArrowExpr Nothing)) = pure mul
                unifyMuls (L _ (ArrowExpr Nothing)) mul@(L _ (ArrowExpr (Just _))) = pure mul
                unifyMuls (L _ (ArrowExpr (Just m1))) mul@(L _ (ArrowExpr (Just m2)))
                    | syntax m1 == syntax m2 = pure mul
                    | otherwise = throwError (MulAnnotationMismatch (location mul) (syntax m1) (syntax m2))

        addTypeDef :: TypeDefinition -> Preprocessor ()
        addTypeDef (TypeDefinition name pArgs mArgs conss) = do
            constructors <- forM conss $ \(L _ (Annotated cons (Just consType))) -> do
                let consName = syntax cons
                    consScheme = typeExprToScheme consType
                modify (dataConstructors %~ M.insert consName consScheme)
                pure (consName, consScheme)
            let tvs = S.unions (map ((^. quantifiedTVars) . fst . snd) constructors)
            modify (dataTypes %~ M.insert (syntax name) (tvs, constructors))
                
        -- TODO: Check type definition well-formedness

