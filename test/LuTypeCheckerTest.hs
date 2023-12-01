module LuTypeCheckerTest where 

import LuTypeChecker
import LuSyntax
import LuTypes
import Data.Map qualified as Map
import Test.HUnit (Counts, Test (..), runTestTT, (~:), (~?=))
import Test.QuickCheck qualified as QC
import LuEvaluator (Store)

store :: EnvironmentTypes
store  = 
  Map.fromList
    [ ("int", IntType),
      ("string", StringType),
      ("boolean", BooleanType),
      ("table1", TableType StringType BooleanType),
      ("table2", TableType StringType IntType),
      ("table3", TableType BooleanType BooleanType),
      ("function1", FunctionType IntType StringType),
      ("function2", FunctionType StringType StringType),
      ("function3", FunctionType IntType IntType),
      ("function4", FunctionType IntType (UnionType IntType StringType))
    ]

{-
===================================================================
======================= Checker: Unit Tests =======================
===================================================================
-}

-- Test checker function with Var as input
test_checkerVar :: Test
test_checkerVar =
    "checker Var" ~:
        TestList
            [ 
                checker (Var (Name "int")) IntType store ~?= True,
                checker (Var (Name "string")) IntType store ~?= False,
                checker (Var (Name "string")) StringType store ~?= True,
                checker (Var (Name "int")) StringType store ~?= False,
                checker (Var (Name "boolean")) BooleanType store ~?= True,
                checker (Var (Name "int")) BooleanType store ~?= False,
                checker (Var (Name "table1")) (TableType StringType BooleanType) store ~?= True,
                checker (Var (Name "table2")) (TableType StringType BooleanType) store ~?= False,
                checker (Var (Name "table3")) (TableType StringType BooleanType) store ~?= False,
                checker (Var (Name "function1")) (FunctionType IntType StringType) store ~?= True,
                checker (Var (Name "function2")) (FunctionType IntType StringType) store ~?= False,
                checker (Var (Name "function3")) (FunctionType IntType StringType) store ~?= False,
                checker (Var (Name "function4")) (FunctionType IntType StringType) store ~?= False,
                checker (Var (Name "function4")) (FunctionType IntType (UnionType IntType StringType)) store ~?= True,
                checker (Var (Name "function1")) (FunctionType IntType (UnionType IntType StringType)) store ~?= False
            ]

-- Test checker function with Val as input
test_checkerVal :: Test
test_checkerVal =
    "checker Val" ~:
        TestList
            [ 
                checker (Val (IntVal 0)) IntType store ~?= True,
                checker (Val (StringVal "")) IntType store ~?= False,
                checker (Val (StringVal "")) StringType store ~?= True,
                checker (Val (IntVal 0)) StringType store ~?= False,
                checker (Val (BoolVal True)) BooleanType store ~?= True,
                checker (Val (IntVal 0)) BooleanType store ~?= False,
                checker (Val (FunctionVal [("x", IntType)] StringType (Block []))) (FunctionType IntType StringType) store ~?= True,
                checker (Val (FunctionVal [("x", StringType)] StringType (Block []))) (FunctionType IntType StringType) store ~?= False,
                checker (Val (FunctionVal [("x", IntType)] IntType (Block []))) (FunctionType IntType StringType) store ~?= False
            ]

-- Test checker function with Op1 as input
test_checkerOp1 :: Test
test_checkerOp1 =
    "checker Op1" ~:
        TestList
            [ 
                checker (Op1 Neg (Var (Name "int"))) IntType store ~?= True,
                checker (Op1 Neg (Var (Name "string"))) IntType store ~?= False,
                checker (Op1 Not (Var (Name "boolean"))) BooleanType store ~?= True,
                checker (Op1 Not (Var (Name "int"))) BooleanType store ~?= False,
                checker (Op1 Len (Var (Name "string"))) IntType store ~?= True,
                checker (Op1 Len (Var (Name "int"))) IntType store ~?= False
            ]

-- Test checker function with Op2 as input
test_checkerOp2 :: Test
test_checkerOp2 =
    "checker Op2" ~:
        TestList
            [ 
                checker (Op2 (Var (Name "int")) Plus (Var (Name "int"))) IntType store ~?= True,
                checker (Op2 (Var (Name "string")) Plus (Var (Name "int"))) IntType store ~?= False,
                checker (Op2 (Var (Name "int")) Minus (Var (Name "int"))) IntType store ~?= True,
                checker (Op2 (Var (Name "boolean")) Minus (Var (Name "int"))) IntType store ~?= False,
                checker (Op2 (Var (Name "int")) Times (Var (Name "int"))) IntType store ~?= True,
                checker (Op2 (Var (Name "string")) Times (Var (Name "int"))) IntType store ~?= False,
                checker (Op2 (Var (Name "int")) Divide (Var (Name "int"))) IntType store ~?= True,
                checker (Op2 (Var (Name "boolean")) Divide (Var (Name "int"))) IntType store ~?= False,
                checker (Op2 (Var (Name "int")) Modulo (Var (Name "int"))) IntType store ~?= True,
                checker (Op2 (Var (Name "string")) Modulo (Var (Name "int"))) IntType store ~?= False,
                checker (Op2 (Var (Name "int")) Eq (Var (Name "int"))) BooleanType store ~?= True,
                checker (Op2 (Var (Name "int")) Eq (Var (Name "string"))) BooleanType store ~?= False,
                checker (Op2 (Var (Name "string")) Gt (Var (Name "string"))) BooleanType store ~?= True,
                checker (Op2 (Var (Name "string")) Gt (Var (Name "boolean"))) BooleanType store ~?= False,
                checker (Op2 (Var (Name "boolean")) Ge (Var (Name "boolean"))) BooleanType store ~?= True,
                checker (Op2 (Var (Name "boolean")) Ge (Var (Name "int"))) BooleanType store ~?= False,
                checker (Op2 (Var (Name "string")) Lt (Var (Name "string"))) BooleanType store ~?= True,
                checker (Op2 (Var (Name "string")) Lt (Var (Name "int"))) BooleanType store ~?= False,
                checker (Op2 (Var (Name "boolean")) Le (Var (Name "boolean"))) BooleanType store ~?= True,
                checker (Op2 (Var (Name "boolean")) Le (Var (Name "string"))) BooleanType store ~?= False,
                checker (Op2 (Var (Name "string")) Concat (Var (Name "string"))) StringType store ~?= True,
                checker (Op2 (Var (Name "string")) Concat (Var (Name "int"))) StringType store ~?= False
            ]

-- Test checker function with TableConst as input
test_checkerTableConst :: Test
test_checkerTableConst =
    "checker TableConst" ~:
        TestList
            [ 
                checker (TableConst [FieldName "x" (Var (Name "int")), FieldName "y" (Var (Name "int"))]) (TableType StringType IntType) store ~?= True,
                checker (TableConst [FieldName "x" (Var (Name "int")), FieldName "y" (Var (Name "string"))]) (TableType StringType IntType) store ~?= False,
                checker (TableConst [FieldKey (Var (Name "string")) (Var (Name "int")), FieldKey (Var (Name "string")) (Var (Name "int"))]) (TableType StringType IntType) store ~?= True,
                checker (TableConst [FieldKey (Var (Name "string")) (Var (Name "int")), FieldKey (Var (Name "string")) (Var (Name "string"))]) (TableType StringType IntType) store ~?= False,
                checker (TableConst [FieldKey (Var (Name "string")) (Var (Name "int")), FieldKey (Var (Name "int")) (Var (Name "int"))]) (TableType StringType IntType) store ~?= False
            ]

-- Test checker function with Call as input
test_checkerCall :: Test
test_checkerCall =
    "checker Call" ~:
        TestList
            [ 
                checker (Call (Name "function1") [Var (Name "int"), Var (Name "string")]) (FunctionType IntType (FunctionType IntType StringType)) store ~?= True,
                checker (Call (Name "function1") [Var (Name "int"), Var (Name "string")]) (FunctionType IntType (FunctionType IntType StringType)) store ~?= False,
                checker (Call (Name "function1") [Var (Name "String"), Var (Name "string")]) (FunctionType IntType (FunctionType IntType StringType)) store ~?= False,
                checker (Call (Name "function1") [Var (Name "int")]) (FunctionType IntType (FunctionType IntType StringType)) store ~?= False,
                checker (Call (Name "function4") [Var (Name "int")]) (FunctionType IntType (UnionType IntType StringType)) store ~?= True,
                checker (Call (Name "function4") [Var (Name "string")]) (FunctionType IntType (UnionType IntType StringType)) store ~?= True,
                checker (Call (Name "function4") [Var (Name "boolean")]) (FunctionType IntType (UnionType IntType StringType)) store ~?= False
            ]

{-
===================================================================
====================== Synthesis: Unit Tests ======================
===================================================================
-}

-- Test synthesis function with Var as input
test_synthesisVar :: Test
test_synthesisVar =
    "synthesis Var" ~:
        TestList
            [ 
                synthesis (Var (Name "int")) store ~?= IntType,
                synthesis (Var (Name "string")) store ~?= StringType,
                synthesis (Var (Name "boolean")) store ~?= BooleanType,
                synthesis (Var (Name "table1")) store ~?= TableType StringType BooleanType,
                synthesis (Var (Name "function1")) store ~?= FunctionType IntType StringType,
                synthesis (Var (Name "function4")) store ~?= FunctionType IntType (UnionType IntType StringType)
            ]

-- Test synthesis function with Val as input
test_synthesisVal :: Test
test_synthesisVal =
    "synthesis Val" ~:
        TestList
            [ 
                synthesis (Val (IntVal 0)) store ~?= IntType,
                synthesis (Val (StringVal "")) store ~?= StringType,
                synthesis (Val (BoolVal True)) store ~?= BooleanType,
                synthesis (Val (FunctionVal [("x", IntType)] StringType (Block []))) store ~?= FunctionType IntType StringType
            ]

-- Test synthesis function with Op1 as input
test_synthesisOp1 :: Test
test_synthesisOp1 =
    "synthesis Op1" ~:
        TestList
            [ 
                synthesis (Op1 Neg (Var (Name "int"))) store ~?= IntType,
                synthesis (Op1 Neg (Var (Name "string"))) store ~?= Never,
                synthesis (Op1 Not (Var (Name "boolean"))) store ~?= BooleanType,
                synthesis (Op1 Not (Var (Name "int"))) store ~?= Never,
                synthesis (Op1 Len (Var (Name "string"))) store ~?= IntType,
                synthesis (Op1 Len (Var (Name "int"))) store ~?= Never
            ]

-- Test synthesis function with Op2 as input
test_synthesisOp2 :: Test
test_synthesisOp2 =
    "synthesis Op2" ~:
        TestList
            [ 
                synthesis (Op2 (Var (Name "int")) Plus (Var (Name "int"))) store ~?= IntType,
                synthesis (Op2 (Var (Name "string")) Plus (Var (Name "int"))) store ~?= Never,
                synthesis (Op2 (Var (Name "int")) Minus (Var (Name "int"))) store ~?= IntType,
                synthesis (Op2 (Var (Name "boolean")) Minus (Var (Name "int"))) store ~?= Never,
                synthesis (Op2 (Var (Name "int")) Times (Var (Name "int"))) store ~?= IntType,
                synthesis (Op2 (Var (Name "string")) Times (Var (Name "int"))) store ~?= Never,
                synthesis (Op2 (Var (Name "int")) Divide (Var (Name "int"))) store ~?= IntType,
                synthesis (Op2 (Var (Name "boolean")) Divide (Var (Name "int"))) store ~?= Never,
                synthesis (Op2 (Var (Name "int")) Modulo (Var (Name "int"))) store ~?= IntType,
                synthesis (Op2 (Var (Name "string")) Modulo (Var (Name "int"))) store ~?= Never,
                synthesis (Op2 (Var (Name "int")) Eq (Var (Name "int"))) store ~?= BooleanType,
                synthesis (Op2 (Var (Name "int")) Eq (Var (Name "string"))) store ~?= Never,
                synthesis (Op2 (Var (Name "string")) Gt (Var (Name "string"))) store ~?= BooleanType,
                synthesis (Op2 (Var (Name "string")) Gt (Var (Name "boolean"))) store ~?= Never,
                synthesis (Op2 (Var (Name "boolean")) Ge (Var (Name "boolean"))) store ~?= BooleanType,
                synthesis (Op2 (Var (Name "boolean")) Ge (Var (Name "int"))) store ~?= Never,
                synthesis (Op2 (Var (Name "string")) Lt (Var (Name "string"))) store ~?= BooleanType,
                synthesis (Op2 (Var (Name "string")) Lt (Var (Name "int"))) store ~?= Never,
                synthesis (Op2 (Var (Name "boolean")) Le (Var (Name "boolean"))) store ~?= BooleanType,
                synthesis (Op2 (Var (Name "boolean")) Le (Var (Name "string"))) store ~?= Never,
                synthesis (Op2 (Var (Name "string")) Concat (Var (Name "string"))) store ~?= StringType,
                synthesis (Op2 (Var (Name "string")) Concat (Var (Name "int"))) store ~?= Never
            ]

-- Test synthesis function with TableConst as input
test_synthesisTableConst :: Test
test_synthesisTableConst =
    "synthesis TableConst" ~:
        TestList
            [ 
                synthesis (TableConst [FieldName "x" (Var (Name "int")), FieldName "y" (Var (Name "int"))]) store ~?= TableType StringType IntType,
                synthesis (TableConst [FieldName "x" (Var (Name "int")), FieldName "y" (Var (Name "string"))]) store ~?= Never,
                synthesis (TableConst [FieldKey (Var (Name "string")) (Var (Name "int")), FieldKey (Var (Name "string")) (Var (Name "int"))]) store ~?= TableType StringType IntType,
                synthesis (TableConst [FieldKey (Var (Name "string")) (Var (Name "int")), FieldKey (Var (Name "string")) (Var (Name "string"))]) store ~?= Never,
                synthesis (TableConst [FieldKey (Var (Name "string")) (Var (Name "int")), FieldKey (Var (Name "int")) (Var (Name "int"))]) store ~?= Never
            ]

-- Test synthesis function with Call as input
test_synthesisCall :: Test
test_synthesisCall =
    "synthesis Call" ~:
        TestList
            [ 
                synthesis (Call (Name "function1") [Var (Name "int"), Var (Name "string")]) store ~?= FunctionType IntType (FunctionType IntType StringType),
                synthesis (Call (Name "function1") [Var (Name "int"), Var (Name "string")]) store ~?= Never,
                synthesis (Call (Name "function1") [Var (Name "String"), Var (Name "string")]) store ~?= Never,
                synthesis (Call (Name "function1") [Var (Name "int")]) store ~?= Never,
                synthesis (Call (Name "function4") [Var (Name "int")]) store ~?= FunctionType IntType (UnionType IntType StringType),
                synthesis (Call (Name "function4") [Var (Name "string")]) store ~?= FunctionType IntType (UnionType IntType StringType),
                synthesis (Call (Name "function4") [Var (Name "boolean")]) store ~?= Never
            ]

{-
===================================================================
================== TypeChecker: QuickCheck Tests ==================
===================================================================
-}

-- Quickcheck property for checker function
prop_checker :: Expression -> LType -> Bool
prop_checker e t = checker e t store == (synthesis e store == t)

-- Quickcheck property for synthesis function
prop_synthesis :: Expression -> Bool
prop_synthesis e = checker e (synthesis e store) store