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
      ("function2", FunctionType IntType IntType)
      
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
                checker (Var (Name "function3")) (FunctionType IntType StringType) store ~?= False
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
                checker (Call (Name "int") [Var (Name "int"), Var (Name "string")]) (FunctionType IntType (FunctionType IntType StringType)) store ~?= True,
                checker (Call (Name "string") [Var (Name "int"), Var (Name "string")]) (FunctionType IntType (FunctionType IntType StringType)) store ~?= False,
                checker (Call (Name "int") [Var (Name "String"), Var (Name "string")]) (FunctionType IntType (FunctionType IntType StringType)) store ~?= False,
                checker (Call (Name "int") [Var (Name "int")]) (FunctionType IntType (FunctionType IntType StringType)) store ~?= False
            ]