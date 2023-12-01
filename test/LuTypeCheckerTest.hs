module LuTypeCheckerTest where 

import LuTypeChecker
import LuSyntax
import LuTypes
import Data.Map qualified as Map
import Test.HUnit (Counts, Test (..), runTestTT, (~:), (~?=))
import Test.QuickCheck qualified as QC
import LuEvaluator (Store)

{-
===================================================================
======================= Checker: Unit Tests =======================
===================================================================
-}

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
