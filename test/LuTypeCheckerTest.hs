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
      ("int-or-string", UnionType IntType StringType), 
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
======================= Helper Functions: Unit Tests ==============
===================================================================
-}
test_isTypeInstanceOf :: Test 
test_isTypeInstanceOf = 
    "isTypeInstanceOf" ~: 
        TestList 
            [ 
                isTypeInstanceOf (UnionType IntType StringType) (UnionType IntType StringType) ~?= True, 
                isTypeInstanceOf (UnionType IntType StringType) IntType ~?= False, 
                isTypeInstanceOf IntType (UnionType IntType StringType) ~?= True, 
                isTypeInstanceOf StringType (UnionType IntType StringType) ~?= True, 
                isTypeInstanceOf (UnionType IntType StringType) (UnionType IntType (UnionType StringType BooleanType)) ~?= True,
                isTypeInstanceOf (UnionType IntType (UnionType StringType BooleanType)) (UnionType IntType StringType) ~?= False, 
                isTypeInstanceOf AnyType IntType ~?= False, 
                isTypeInstanceOf IntType AnyType ~?= True, 
                isTypeInstanceOf AnyType AnyType ~?= True
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
                checker store (Var (Name "int")) IntType ~?= True,
                checker store (Var (Name "string")) IntType ~?= False,
                checker store (Var (Name "string")) StringType ~?= True,
                checker store (Var (Name "int")) StringType ~?= False,
                checker store (Var (Name "boolean")) BooleanType ~?= True,
                checker store (Var (Name "int")) BooleanType ~?= False,
                checker store (Var (Name "table1")) (TableType StringType BooleanType) ~?= True,
                checker store (Var (Name "table2")) (TableType StringType BooleanType) ~?= False,
                checker store (Var (Name "table3")) (TableType StringType BooleanType) ~?= False,
                checker store (Var (Name "function1")) (FunctionType IntType StringType) ~?= True,
                checker store (Var (Name "function2")) (FunctionType IntType StringType) ~?= False,
                checker store (Var (Name "function3")) (FunctionType IntType StringType) ~?= False,
                checker store (Var (Name "function4")) (FunctionType IntType StringType) ~?= False,
                checker store (Var (Name "function4")) (FunctionType IntType (UnionType IntType StringType)) ~?= True,
                checker store (Var (Name "function1")) (FunctionType IntType (UnionType IntType StringType)) ~?= False
            ]

-- Test checker function with Val as input
test_checkerVal :: Test
test_checkerVal =
    "checker Val" ~:
        TestList
            [ 
                checker store (Val (IntVal 0)) IntType ~?= True,
                checker store (Val (StringVal "")) IntType ~?= False,
                checker store (Val (StringVal "")) StringType ~?= True,
                checker store (Val (IntVal 0)) StringType ~?= False,
                checker store (Val (BoolVal True)) BooleanType ~?= True,
                checker store (Val (IntVal 0)) BooleanType ~?= False,
                checker store (Val (FunctionVal [("x", IntType)] StringType (Block []))) (FunctionType IntType StringType) ~?= True,
                checker store (Val (FunctionVal [("x", StringType)] StringType (Block []))) (FunctionType IntType StringType) ~?= False,
                checker store (Val (FunctionVal [("x", IntType)] IntType (Block []))) (FunctionType IntType StringType) ~?= False
            ]

-- Test checker function with Op1 as input
test_checkerOp1 :: Test
test_checkerOp1 =
    "checker Op1" ~:
        TestList
            [ 
                checker store (Op1 Neg (Var (Name "int"))) IntType ~?= True,
                checker store (Op1 Neg (Var (Name "string"))) IntType ~?= False,
                checker store (Op1 Not (Var (Name "boolean"))) BooleanType ~?= True,
                checker store (Op1 Not (Var (Name "int"))) BooleanType ~?= True,
                checker store (Op1 Len (Var (Name "string"))) IntType ~?= True,
                checker store (Op1 Len (Var (Name "int"))) IntType ~?= True
            ]

-- Test checker function with Op2 as input
test_checkerOp2 :: Test
test_checkerOp2 =
    "checker Op2" ~:
        TestList
            [ 
                checker store (Op2 (Var (Name "int")) Plus (Var (Name "int"))) IntType ~?= True,
                checker store (Op2 (Var (Name "string")) Plus (Var (Name "int"))) IntType ~?= False,
                checker store (Op2 (Var (Name "int")) Minus (Var (Name "int"))) IntType ~?= True,
                checker store (Op2 (Var (Name "boolean")) Minus (Var (Name "int"))) IntType ~?= False,
                checker store (Op2 (Var (Name "int")) Times (Var (Name "int"))) IntType ~?= True,
                checker store (Op2 (Var (Name "string")) Times (Var (Name "int"))) IntType ~?= False,
                checker store (Op2 (Var (Name "int")) Divide (Var (Name "int"))) IntType ~?= True,
                checker store (Op2 (Var (Name "boolean")) Divide (Var (Name "int"))) IntType ~?= False,
                checker store (Op2 (Var (Name "int")) Modulo (Var (Name "int"))) IntType ~?= True,
                checker store (Op2 (Var (Name "string")) Modulo (Var (Name "int"))) IntType ~?= False,
                checker store (Op2 (Var (Name "int")) Eq (Var (Name "int"))) BooleanType ~?= True,
                checker store (Op2 (Var (Name "int")) Eq (Var (Name "string"))) BooleanType ~?= False,
                checker store (Op2 (Var (Name "string")) Gt (Var (Name "string"))) BooleanType ~?= True,
                checker store (Op2 (Var (Name "string")) Gt (Var (Name "boolean"))) BooleanType ~?= False,
                checker store (Op2 (Var (Name "boolean")) Ge (Var (Name "boolean"))) BooleanType ~?= True,
                checker store (Op2 (Var (Name "boolean")) Ge (Var (Name "int"))) BooleanType ~?= False,
                checker store (Op2 (Var (Name "string")) Lt (Var (Name "string"))) BooleanType ~?= True,
                checker store (Op2 (Var (Name "string")) Lt (Var (Name "int"))) BooleanType ~?= False,
                checker store (Op2 (Var (Name "boolean")) Le (Var (Name "boolean"))) BooleanType ~?= True,
                checker store (Op2 (Var (Name "boolean")) Le (Var (Name "string"))) BooleanType ~?= False,
                checker store (Op2 (Var (Name "string")) Concat (Var (Name "string"))) StringType ~?= True,
                checker store (Op2 (Var (Name "string")) Concat (Var (Name "int"))) StringType ~?= False
            ]

-- Test checker function with TableConst as input
test_checkerTableConst :: Test
test_checkerTableConst =
    "checker TableConst" ~:
        TestList
            [ 
                checker store (TableConst [FieldName "x" (Var (Name "int")), FieldName "y" (Var (Name "int"))]) (TableType StringType IntType) ~?= True,
                checker store (TableConst [FieldName "x" (Var (Name "int")), FieldName "y" (Var (Name "string"))]) (TableType StringType IntType) ~?= False,
                checker store (TableConst [FieldKey (Var (Name "string")) (Var (Name "int")), FieldKey (Var (Name "string")) (Var (Name "int"))]) (TableType StringType IntType) ~?= True,
                checker store (TableConst [FieldKey (Var (Name "string")) (Var (Name "int")), FieldKey (Var (Name "string")) (Var (Name "string"))]) (TableType StringType IntType) ~?= False,
                checker store (TableConst [FieldKey (Var (Name "string")) (Var (Name "int")), FieldKey (Var (Name "int")) (Var (Name "int"))]) (TableType StringType IntType) ~?= False
            ]

-- Test checker function with Call as input
test_checkerCall :: Test
test_checkerCall =
    "checker Call" ~:
        TestList
            [ 
                checker store (Call (Name "function1") [Var (Name "int"), Var (Name "string")]) (FunctionType IntType (FunctionType IntType StringType)) ~?= False,
                checker store (Call (Name "function1") [Var (Name "int"), Var (Name "string")]) (FunctionType IntType (FunctionType IntType StringType)) ~?= False,
                checker store (Call (Name "function1") [Var (Name "String"), Var (Name "string")]) (FunctionType IntType (FunctionType IntType StringType)) ~?= False,
                checker store (Call (Name "function1") [Var (Name "int")]) (FunctionType IntType (FunctionType IntType StringType)) ~?= False,
                checker store (Call (Name "function4") [Var (Name "int")]) (UnionType IntType StringType) ~?= True,
                checker store (Call (Name "function4") [Var (Name "string")]) (UnionType IntType StringType) ~?= False,
                checker store (Call (Name "function4") [Var (Name "boolean")]) (FunctionType IntType (UnionType IntType StringType)) ~?= False
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
                synthesis store (Var (Name "int")) ~?= IntType,
                synthesis store (Var (Name "string")) ~?= StringType,
                synthesis store (Var (Name "boolean")) ~?= BooleanType,
                synthesis store (Var (Name "table1")) ~?= TableType StringType BooleanType,
                synthesis store (Var (Name "function1")) ~?= FunctionType IntType StringType,
                synthesis store (Var (Name "function4")) ~?= FunctionType IntType (UnionType IntType StringType), 
                synthesis store (Var (Dot (Var (Name "table1")) "n")) ~?= BooleanType
            ]

-- Test synthesis function with Val as input
test_synthesisVal :: Test
test_synthesisVal =
    "synthesis Val" ~:
        TestList
            [ 
                synthesis store (Val (IntVal 0)) ~?= IntType,
                synthesis store (Val (StringVal "")) ~?= StringType,
                synthesis store (Val (BoolVal True)) ~?= BooleanType,
                synthesis store (Val (FunctionVal [("x", IntType)] StringType (Block []))) ~?= FunctionType IntType StringType
            ]

-- Test synthesis function with Op1 as input
test_synthesisOp1 :: Test
test_synthesisOp1 =
    "synthesis Op1" ~:
        TestList
            [ 
                synthesis store (Op1 Neg (Var (Name "int"))) ~?= IntType,
                synthesis store (Op1 Neg (Var (Name "string"))) ~?= Never,
                synthesis store (Op1 Not (Var (Name "boolean"))) ~?= BooleanType,
                synthesis store (Op1 Not (Var (Name "int"))) ~?= BooleanType,
                synthesis store (Op1 Len (Var (Name "string"))) ~?= IntType,
                synthesis store (Op1 Len (Var (Name "int"))) ~?= IntType
            ]

-- Test synthesis function with Op2 as input
test_synthesisOp2 :: Test
test_synthesisOp2 =
    "synthesis Op2" ~:
        TestList
            [ 
                synthesis store (Op2 (Var (Name "int")) Plus (Var (Name "int"))) ~?= IntType,
                synthesis store (Op2 (Var (Name "string")) Plus (Var (Name "int"))) ~?= Never,
                synthesis store (Op2 (Var (Name "int")) Minus (Var (Name "int"))) ~?= IntType,
                synthesis store (Op2 (Var (Name "boolean")) Minus (Var (Name "int"))) ~?= Never,
                synthesis store (Op2 (Var (Name "int")) Times (Var (Name "int"))) ~?= IntType,
                synthesis store (Op2 (Var (Name "string")) Times (Var (Name "int"))) ~?= Never,
                synthesis store (Op2 (Var (Name "int")) Divide (Var (Name "int"))) ~?= IntType,
                synthesis store (Op2 (Var (Name "boolean")) Divide (Var (Name "int"))) ~?= Never,
                synthesis store (Op2 (Var (Name "int")) Modulo (Var (Name "int"))) ~?= IntType,
                synthesis store (Op2 (Var (Name "string")) Modulo (Var (Name "int"))) ~?= Never,
                synthesis store (Op2 (Var (Name "int")) Eq (Var (Name "int"))) ~?= BooleanType,
                synthesis store (Op2 (Var (Name "int")) Eq (Var (Name "string"))) ~?= Never,
                synthesis store (Op2 (Var (Name "string")) Gt (Var (Name "string"))) ~?= BooleanType,
                synthesis store (Op2 (Var (Name "string")) Gt (Var (Name "boolean"))) ~?= Never,
                synthesis store (Op2 (Var (Name "boolean")) Ge (Var (Name "boolean"))) ~?= BooleanType,
                synthesis store (Op2 (Var (Name "boolean")) Ge (Var (Name "int"))) ~?= Never,
                synthesis store (Op2 (Var (Name "string")) Lt (Var (Name "string"))) ~?= BooleanType,
                synthesis store (Op2 (Var (Name "string")) Lt (Var (Name "int"))) ~?= Never,
                synthesis store (Op2 (Var (Name "boolean")) Le (Var (Name "boolean"))) ~?= BooleanType,
                synthesis store (Op2 (Var (Name "boolean")) Le (Var (Name "string"))) ~?= Never,
                synthesis store (Op2 (Var (Name "string")) Concat (Var (Name "string"))) ~?= StringType,
                synthesis store (Op2 (Var (Name "string")) Concat (Var (Name "int"))) ~?= Never
            ]

-- Test synthesis function with TableConst as input
test_synthesisTableConst :: Test
test_synthesisTableConst =
    "synthesis TableConst" ~:
        TestList
            [ 
                synthesis store (TableConst [FieldName "x" (Var (Name "int")), FieldName "y" (Var (Name "int"))]) ~?= TableType StringType IntType,
                synthesis store (TableConst [FieldName "x" (Var (Name "int")), FieldName "y" (Var (Name "string"))]) ~?= TableType StringType (UnionType IntType StringType),
                synthesis store (TableConst [FieldKey (Var (Name "string")) (Var (Name "int")), FieldKey (Var (Name "string")) (Var (Name "int"))]) ~?= TableType StringType IntType,
                synthesis store (TableConst [FieldKey (Var (Name "string")) (Var (Name "int")), FieldKey (Var (Name "string")) (Var (Name "string"))]) ~?= TableType StringType (UnionType IntType StringType),
                synthesis store (TableConst [FieldKey (Var (Name "string")) (Var (Name "int")), FieldKey (Var (Name "int")) (Var (Name "int"))]) ~?= TableType (UnionType StringType IntType) IntType, 
                synthesis store (TableConst [FieldKey (Var (Name "int-or-string")) (Var (Name "int")), FieldKey (Var (Name "string")) (Var (Name "int"))]) ~?= TableType (UnionType IntType StringType) IntType
            ]

-- Test synthesis function with Call as input
test_synthesisCall :: Test
test_synthesisCall =
    "synthesis Call" ~:
        TestList
            [ 
                synthesis store (Call (Name "function1") [Var (Name "int"), Var (Name "string")]) ~?= Never,
                synthesis store (Call (Name "function1") [Var (Name "String"), Var (Name "string")]) ~?= Never,
                synthesis store (Call (Name "function1") [Var (Name "int")]) ~?= StringType,
                synthesis store (Call (Name "function4") [Var (Name "int")]) ~?= UnionType IntType StringType,
                synthesis store (Call (Name "function4") [Var (Name "string")]) ~?= Never, 
                synthesis store (Call (Name "function4") [Var (Name "boolean")]) ~?= Never, 
                synthesis store (Call (Name "function4") [Var (Name "int")]) ~?= UnionType IntType StringType
            ]

test :: IO Counts 
test = runTestTT $ TestList [test_isTypeInstanceOf, test_checkerVar, test_checkerVal, test_checkerOp1, test_checkerOp2, test_checkerTableConst, test_checkerCall, test_synthesisVar, test_synthesisVal, test_synthesisOp1, test_synthesisOp2, test_synthesisTableConst, test_synthesisCall]
{-
===================================================================
================== TypeChecker: QuickCheck Tests ==================
===================================================================
-}

-- Quickcheck property for checker function
prop_checker :: Expression -> LType -> Bool
prop_checker e t = checker store e t == (synthesis store e == t)

-- Quickcheck property for synthesis function
prop_synthesis :: Expression -> Bool
prop_synthesis e = checker store e (synthesis store e)

qc :: IO ()
qc = do
  putStrLn "synthesis"
  QC.quickCheck prop_synthesis
  putStrLn "checker"
  QC.quickCheck prop_checker