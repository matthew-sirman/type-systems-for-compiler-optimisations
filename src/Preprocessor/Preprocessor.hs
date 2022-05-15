module Preprocessor.Preprocessor where

import Parser.AST
import Parser.Parser
import Typing.Types
import Error.Error (showContext)

import Control.Monad.Except
import Control.Monad.State
import Control.Lens
import qualified Data.HashMap.Strict as M
import qualified Data.HashSet as S
import Data.List (intercalate)

import System.Directory

data PreprocessorError
    = NoMatchingImplementation SourceLocation Identifier
    | TypeAnnotationMismatch SourceLocation TypeExpr TypeExpr
    | MulAnnotationMismatch SourceLocation MultiplicityExpr MultiplicityExpr
    | ImportNotFound SourceLocation String
    | ParserError String

showPPError :: String -> PreprocessorError -> String
showPPError text (NoMatchingImplementation sl name) =
    showContext text sl ++ "No matching implementation for function \"" ++ show name ++ "\"."
showPPError text (TypeAnnotationMismatch sl ty ty') =
    showContext text sl ++ "Type annotation conflict between \"" ++ show ty ++ "\" and \"" ++ show ty' ++ "\"."
showPPError text (MulAnnotationMismatch sl m m') =
    showContext text sl ++ "Multiplicity annotation conflict between \"" ++ show m ++ "\" and \"" ++ show m' ++ "\"."
showPPError text (ImportNotFound sl path) =
    showContext text sl ++ "Import file not found \"" ++ path ++ "\"."
showPPError text (ParserError err) = err

type Preprocessor a = StateT (StaticContext, S.HashSet FilePath) (ExceptT PreprocessorError IO) a

transformAST :: [FilePath] -> [Loc Statement] -> StaticContext -> ExceptT PreprocessorError IO (Loc ValExpr, StaticContext)
transformAST paths stmts ctx = do
    (bindings, (ctx', _)) <- runStateT (transform' stmts) (ctx, S.empty)
    let xs = map (slEnd . location) bindings
        endOfFile = maximum (map (slEnd . location) bindings)
        wholeFileLoc = SL 0 endOfFile 1
    pure (L wholeFileLoc (VELet bindings (L wholeFileLoc (VEVar (I "main")))), ctx')
    where
        transform' :: [Loc Statement] -> Preprocessor [Loc LetBinding]
        transform' [] = pure []
        transform' ((L loc (Import path)) : rest) = do
            importedStmts <- tryPaths paths
            importedBindings <- transform' importedStmts
            (importedBindings++) <$> transform' rest
            where
                tryPaths :: [FilePath] -> Preprocessor [Loc Statement]
                tryPaths [] = throwError (ImportNotFound loc (intercalate "." (syntax path)))
                tryPaths (p:ps) = do
                    let filePath = p ++ concatMap ('/':) (syntax path) ++ ".stfl"
                    alreadyLoaded <- gets (S.member filePath . (^. _2))
                    if alreadyLoaded
                       then pure []
                       else do
                           exists <- liftIO $ doesFileExist filePath
                           if exists
                              then do
                                  modify (_2 %~ S.insert filePath)
                                  source <- liftIO $ readFile filePath
                                  case parse source of
                                    Left e -> throwError (ParserError e)
                                    Right stmts -> pure stmts
                           else tryPaths ps

        transform' (tLoc@(L _ (TypeDecl name t)) : fLoc@(L _ (FuncDecl name' body)) : rest)
            | syntax name == syntax name' = do
                embellished <- embellishFunction name t body
                let func = loc embellished tLoc fLoc
                (func:) <$> transform' rest
        transform' (L _ (TypeDecl name _) : _) =
            throwError (NoMatchingImplementation (location name) (syntax name))
        transform' (fLoc@(L _ (FuncDecl name body)):rest) = do
            let mul
                    | syntax name == I "main" = Just (L (location name) (MEAtom Linear))
                    | otherwise = Just (L (location name) (MEAtom Normal))
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
                modify (_1 . dataConstructors %~ M.insert consName consScheme)
                pure (consName, consScheme)
            let tvs = S.unions (map ((^. quantifiedTVars) . fst . snd) constructors)
            modify (_1 . dataTypes %~ M.insert (syntax name) (tvs, constructors))
                
        -- TODO: Check type definition well-formedness

