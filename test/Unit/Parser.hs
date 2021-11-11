module Unit.Parser
    ( parserUnitTests
    ) where

import Parser.Parser

import Test.HUnit

stmtTests :: Test
stmtTests = "stmt" ~:
    [ "type-decl"           ~: test_parseStmt "f : X;;" ~?= Right expectedTypeDecl
    , "func-decl"           ~: test_parseStmt "f = x;;" ~?= Right expectedFuncDecl
    , "func-decl-params"    ~: test_parseStmt "f x = x;;" ~?= Right expectedParamDecl
    ]
    where
        expectedTypeDecl = TypeDecl "f" (TEConcrete "X")
        expectedFuncDecl = FuncDecl "f" (VEVar "x")
        expectedParamDecl = FuncDecl "f" (VELambda (VarPattern (Annotated "x" Nothing)) (Arrow Nothing) (VEVar "x"))

exprTests :: Test
exprTests = "expr" ~:
    [ "let"                 ~: test_parseExpr "let x = y in y" ~?= Right expectedLet
    , "case"                ~: test_parseExpr "case x of | 0 -> y" ~?= Right expectedCase
    , "if-then-else"        ~: test_parseExpr "if False then x else y" ~?= Right expectedIfThenElse
    , "lambda"              ~: test_parseExpr "\\x -o y" ~?= Right expectedLambda
    , "binop"               ~: test_parseExpr "x + y" ~?= Right expectedBinOp
    , "app"                 ~: test_parseExpr "x 0" ~?= Right expectedApp
    , "var"                 ~: test_parseExpr "x_'" ~?= Right expectedVar
    , "constructor"         ~: test_parseExpr "Xy" ~?= Right expectedConstructor
    , "int-lit"             ~: test_parseExpr "123" ~?= Right expectedIntLit
    , "real-lit"            ~: test_parseExpr "10.5" ~?= Right expectedRealLit
    , "tuple"               ~: test_parseExpr "(x, y, z)" ~?= Right expectedTuple
    , "list"                ~: test_parseExpr "[x, y, z]" ~?= Right expectedList
    ]
    where
        expectedLet = VELet (VarPattern (Annotated "x" Nothing)) (VEVar "y") (VEVar "y")
        expectedCase = VECase (VEVar "x") [CaseBranch (LitPattern (IntLiteral 0)) (Arrow (Just Normal)) (VEVar "y")]
        expectedIfThenElse = VEIfThenElse (VECons "False") (VEVar "x") (VEVar "y")
        expectedLambda = VELambda (VarPattern (Annotated "x" Nothing)) (Arrow (Just Linear)) (VEVar "y")
        expectedBinOp = VEBinOp BinOpPlus (VEVar "x") (VEVar "y")
        expectedApp = VEApp (VEVar "x") (VELiteral (IntLiteral 0))
        expectedVar = VEVar "x_'"
        expectedConstructor = VECons "Xy"
        expectedIntLit = VELiteral (IntLiteral 123)
        expectedRealLit = VELiteral (RealLiteral 10.5)
        expectedTuple = VETuple [VEVar "x", VEVar "y", VEVar "z"]
        expectedList = VELiteral (ListLiteral [VEVar "x", VEVar "y", VEVar "z"])

parserUnitTests :: Test
parserUnitTests = "parser" ~:
    [ stmtTests
    , exprTests
    ]

