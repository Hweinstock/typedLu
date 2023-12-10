module LuTypeCheckerTest where 

import LuTypeChecker
import LuSyntax
import LuTypes
import State qualified as S
import Context qualified as C
import Data.Map qualified as Map
import Test.HUnit (Counts, Test (..), runTestTT, (~:), (~?=))
import Test.QuickCheck qualified as QC
import LuEvaluator (Store)

store :: TypeEnv
store = C.setGMap typeMap emptyTypeEnv where 
  typeMap = Map.fromList
    [ (StringVal "int", IntType),
      (StringVal "string", StringType),
      (StringVal "boolean", BooleanType),
      (StringVal "int-or-string", UnionType IntType StringType), 
      (StringVal "table1", TableType StringType BooleanType),
      (StringVal "table2", TableType StringType IntType),
      (StringVal "table3", TableType BooleanType BooleanType),
      (StringVal "function0", FunctionType Never StringType),
      (StringVal "function1", FunctionType IntType StringType),
      (StringVal "function2", FunctionType StringType StringType),
      (StringVal "function3", FunctionType IntType IntType),
      (StringVal "function4", FunctionType IntType (UnionType IntType StringType))
    ]

{-
===================================================================
======================= Helper Functions: Unit Tests ==============
===================================================================
-}
test_isSubtype:: Test 
test_isSubtype = 
    "test_isSubtype" ~: 
        TestList 
            [ 
                (<:) (UnionType IntType StringType) (UnionType IntType StringType) ~?= True, 
                (<:) (UnionType IntType StringType) IntType ~?= False, 
                (<:) IntType (UnionType IntType StringType) ~?= True, 
                (<:) StringType (UnionType IntType StringType) ~?= True, 
                (<:) (UnionType IntType StringType) (UnionType IntType (UnionType StringType BooleanType)) ~?= True,
                (<:) (UnionType IntType (UnionType StringType BooleanType)) (UnionType IntType StringType) ~?= False, 
                (<:) AnyType IntType ~?= False, 
                (<:) IntType AnyType ~?= True, 
                (<:) AnyType AnyType ~?= True, 
                FunctionType (UnionType IntType StringType) IntType <: FunctionType IntType IntType ~?= True, 
                FunctionType IntType IntType <: FunctionType IntType (UnionType IntType StringType) ~?= True, 
                FunctionType IntType (UnionType IntType StringType) <: FunctionType IntType IntType ~?= False, 
                FunctionType IntType IntType <: FunctionType (UnionType IntType StringType) IntType ~?= False, 
                FunctionType IntType StringType <: FunctionType IntType (UnionType IntType StringType) ~?= True, 
                FunctionType (UnionType IntType StringType) (FunctionType IntType IntType) <: FunctionType IntType (FunctionType IntType IntType) ~?= True, 
                FunctionType IntType (FunctionType IntType IntType) <: FunctionType IntType (FunctionType IntType IntType) ~?= True, 
                FunctionType IntType (FunctionType IntType StringType) <: FunctionType IntType (FunctionType IntType StringType) ~?= True,
                FunctionType IntType (FunctionType IntType (UnionType BooleanType StringType)) <: FunctionType IntType (FunctionType IntType StringType) ~?= False

            ]


{-
===================================================================
======================= Checker: Unit Tests =======================
===================================================================
-}

-- Test runChecker function with Var as input
test_checkerVar :: Test
test_checkerVar =
    "runChecker Var" ~:
        TestList
            [ 
                runChecker store (Var (Name "int")) IntType ~?= True,
                runChecker store (Var (Name "string")) IntType ~?= False,
                runChecker store (Var (Name "string")) StringType ~?= True,
                runChecker store (Var (Name "int")) StringType ~?= False,
                runChecker store (Var (Name "boolean")) BooleanType ~?= True,
                runChecker store (Var (Name "int")) BooleanType ~?= False,
                runChecker store (Var (Name "table1")) (TableType StringType BooleanType) ~?= True,
                runChecker store (Var (Name "table2")) (TableType StringType BooleanType) ~?= False,
                runChecker store (Var (Name "table3")) (TableType StringType BooleanType) ~?= False,
                runChecker store (Var (Name "function1")) (FunctionType IntType StringType) ~?= True,
                runChecker store (Var (Name "function2")) (FunctionType IntType StringType) ~?= False,
                runChecker store (Var (Name "function3")) (FunctionType IntType StringType) ~?= False,
                runChecker store (Var (Name "function4")) (FunctionType IntType StringType) ~?= False,
                runChecker store (Var (Name "function4")) (FunctionType IntType (UnionType IntType StringType)) ~?= True,
                runChecker store (Var (Name "function1")) (FunctionType IntType (UnionType IntType StringType)) ~?= True
            ]

-- Test runChecker function with Val as input
test_checkerVal :: Test
test_checkerVal =
    "runChecker Val" ~:
        TestList
            [ 
                runChecker store (Val (IntVal 0)) IntType ~?= True,
                runChecker store (Val (StringVal "")) IntType ~?= False,
                runChecker store (Val (StringVal "")) StringType ~?= True,
                runChecker store (Val (IntVal 0)) StringType ~?= False,
                runChecker store (Val (BoolVal True)) BooleanType ~?= True,
                runChecker store (Val (IntVal 0)) BooleanType ~?= False,
                runChecker store (Val (FunctionVal [("x", IntType)] StringType (Block []))) (FunctionType IntType StringType) ~?= True,
                runChecker store (Val (FunctionVal [("x", StringType)] StringType (Block []))) (FunctionType IntType StringType) ~?= False,
                runChecker store (Val (FunctionVal [("x", IntType)] IntType (Block []))) (FunctionType IntType StringType) ~?= False, 
                runChecker store (Val (StringVal "")) (UnionType StringType IntType) ~?= True
            ]

-- Test runChecker function with Op1 as input
test_checkerOp1 :: Test
test_checkerOp1 =
    "runChecker Op1" ~:
        TestList
            [ 
                runChecker store (Op1 Neg (Var (Name "int"))) IntType ~?= True,
                runChecker store (Op1 Neg (Var (Name "string"))) IntType ~?= False,
                runChecker store (Op1 Not (Var (Name "boolean"))) BooleanType ~?= True,
                runChecker store (Op1 Not (Var (Name "int"))) BooleanType ~?= True,
                runChecker store (Op1 Len (Var (Name "string"))) IntType ~?= True,
                runChecker store (Op1 Len (Var (Name "int"))) IntType ~?= True, 
                runChecker store (Op1 Not (Val NilVal)) (UnionType IntType BooleanType) ~?= True
            ]

-- Test runChecker function with Op2 as input
test_checkerOp2 :: Test
test_checkerOp2 =
    "runChecker Op2" ~:
        TestList
            [ 
                runChecker store (Op2 (Var (Name "int")) Plus (Var (Name "int"))) IntType ~?= True,
                runChecker store (Op2 (Var (Name "string")) Plus (Var (Name "int"))) IntType ~?= False,
                runChecker store (Op2 (Var (Name "int")) Minus (Var (Name "int"))) IntType ~?= True,
                runChecker store (Op2 (Var (Name "boolean")) Minus (Var (Name "int"))) IntType ~?= False,
                runChecker store (Op2 (Var (Name "int")) Times (Var (Name "int"))) IntType ~?= True,
                runChecker store (Op2 (Var (Name "string")) Times (Var (Name "int"))) IntType ~?= False,
                runChecker store (Op2 (Var (Name "int")) Divide (Var (Name "int"))) IntType ~?= True,
                runChecker store (Op2 (Var (Name "boolean")) Divide (Var (Name "int"))) IntType ~?= False,
                runChecker store (Op2 (Var (Name "int")) Modulo (Var (Name "int"))) IntType ~?= True,
                runChecker store (Op2 (Var (Name "string")) Modulo (Var (Name "int"))) IntType ~?= False,
                runChecker store (Op2 (Var (Name "int")) Eq (Var (Name "int"))) BooleanType ~?= True,
                runChecker store (Op2 (Var (Name "int")) Eq (Var (Name "string"))) BooleanType ~?= False,
                runChecker store (Op2 (Var (Name "string")) Gt (Var (Name "string"))) BooleanType ~?= True,
                runChecker store (Op2 (Var (Name "string")) Gt (Var (Name "boolean"))) BooleanType ~?= False,
                runChecker store (Op2 (Var (Name "boolean")) Ge (Var (Name "boolean"))) BooleanType ~?= True,
                runChecker store (Op2 (Var (Name "boolean")) Ge (Var (Name "int"))) BooleanType ~?= False,
                runChecker store (Op2 (Var (Name "string")) Lt (Var (Name "string"))) BooleanType ~?= True,
                runChecker store (Op2 (Var (Name "string")) Lt (Var (Name "int"))) BooleanType ~?= False,
                runChecker store (Op2 (Var (Name "boolean")) Le (Var (Name "boolean"))) BooleanType ~?= True,
                runChecker store (Op2 (Var (Name "boolean")) Le (Var (Name "string"))) BooleanType ~?= False,
                runChecker store (Op2 (Var (Name "string")) Concat (Var (Name "string"))) StringType ~?= True,
                runChecker store (Op2 (Var (Name "string")) Concat (Var (Name "int"))) StringType ~?= False
            ]

-- Test runChecker function with TableConst as input
test_checkerTableConst :: Test
test_checkerTableConst =
    "runChecker TableConst" ~:
        TestList
            [ 
                runChecker store (TableConst [FieldName "x" (Var (Name "int")), FieldName "y" (Var (Name "int"))]) (TableType StringType IntType) ~?= True,
                runChecker store (TableConst [FieldName "x" (Var (Name "int")), FieldName "y" (Var (Name "string"))]) (TableType StringType IntType) ~?= False,
                runChecker store (TableConst [FieldKey (Var (Name "string")) (Var (Name "int")), FieldKey (Var (Name "string")) (Var (Name "int"))]) (TableType StringType IntType) ~?= True,
                runChecker store (TableConst [FieldKey (Var (Name "string")) (Var (Name "int")), FieldKey (Var (Name "string")) (Var (Name "string"))]) (TableType StringType IntType) ~?= False,
                runChecker store (TableConst [FieldKey (Var (Name "string")) (Var (Name "int")), FieldKey (Var (Name "int")) (Var (Name "int"))]) (TableType StringType IntType) ~?= False
            ]

-- Test runChecker function with Call as input
test_checkerCall :: Test
test_checkerCall =
    "runChecker Call" ~:
        TestList
            [ 
                runChecker store (Call (Name "function1") [Var (Name "int"), Var (Name "string")]) (FunctionType IntType (FunctionType IntType StringType)) ~?= False,
                runChecker store (Call (Name "function1") [Var (Name "int"), Var (Name "string")]) (FunctionType IntType (FunctionType IntType StringType)) ~?= False,
                runChecker store (Call (Name "function1") [Var (Name "String"), Var (Name "string")]) (FunctionType IntType (FunctionType IntType StringType)) ~?= False,
                runChecker store (Call (Name "function1") [Var (Name "int")]) (FunctionType IntType (FunctionType IntType StringType)) ~?= False,
                runChecker store (Call (Name "function4") [Var (Name "int")]) (UnionType IntType StringType) ~?= True,
                runChecker store (Call (Name "function4") [Var (Name "string")]) (UnionType IntType StringType) ~?= False,
                runChecker store (Call (Name "function4") [Var (Name "boolean")]) (FunctionType IntType (UnionType IntType StringType)) ~?= False
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
                runSynthesis store (Var (Name "int")) ~?= IntType,
                runSynthesis store (Var (Name "string")) ~?= StringType,
                runSynthesis store (Var (Name "boolean")) ~?= BooleanType,
                runSynthesis store (Var (Name "table1")) ~?= TableType StringType BooleanType,
                runSynthesis store (Var (Name "function1")) ~?= FunctionType IntType StringType,
                runSynthesis store (Var (Name "function4")) ~?= FunctionType IntType (UnionType IntType StringType), 
                runSynthesis store (Var (Dot (Var (Name "table1")) "n")) ~?= BooleanType
            ]

-- Test synthesis function with Val as input
test_synthesisVal :: Test
test_synthesisVal =
    "synthesis Val" ~:
        TestList
            [ 
                runSynthesis store (Val (IntVal 0)) ~?= IntType,
                runSynthesis store (Val (StringVal "")) ~?= StringType,
                runSynthesis store (Val (BoolVal True)) ~?= BooleanType,
                runSynthesis store (Val (FunctionVal [("x", IntType)] StringType (Block []))) ~?= FunctionType IntType StringType, 
                runSynthesis store (Val (FunctionVal [("a",IntType)] StringType (Block [Return (Val (StringVal "here"))]))) ~?= FunctionType IntType StringType
            ]

-- Test synthesis function with Op1 as input
test_synthesisOp1 :: Test
test_synthesisOp1 =
    "synthesis Op1" ~:
        TestList
            [ 
                runSynthesis store (Op1 Neg (Var (Name "int"))) ~?= IntType,
                runSynthesis store (Op1 Neg (Var (Name "string"))) ~?= UnknownType,
                runSynthesis store (Op1 Not (Var (Name "boolean"))) ~?= BooleanType,
                runSynthesis store (Op1 Not (Var (Name "int"))) ~?= BooleanType,
                runSynthesis store (Op1 Len (Var (Name "string"))) ~?= IntType,
                runSynthesis store (Op1 Len (Var (Name "int"))) ~?= IntType, 
                runSynthesis store (Op1 Len (Var (Name "table1"))) ~?= IntType, 
                runSynthesis store (Op1 Len (Var (Name "table2"))) ~?= IntType
            ]

-- Test synthesis function with Op2 as input
test_synthesisOp2 :: Test
test_synthesisOp2 =
    "synthesis Op2" ~:
        TestList
            [ 
                runSynthesis store (Op2 (Var (Name "int")) Plus (Var (Name "int"))) ~?= IntType,
                runSynthesis store (Op2 (Var (Name "string")) Plus (Var (Name "int"))) ~?= UnknownType,
                runSynthesis store (Op2 (Var (Name "int")) Minus (Var (Name "int"))) ~?= IntType,
                runSynthesis store (Op2 (Var (Name "boolean")) Minus (Var (Name "int"))) ~?= UnknownType,
                runSynthesis store (Op2 (Var (Name "int")) Times (Var (Name "int"))) ~?= IntType,
                runSynthesis store (Op2 (Var (Name "string")) Times (Var (Name "int"))) ~?= UnknownType,
                runSynthesis store (Op2 (Var (Name "int")) Divide (Var (Name "int"))) ~?= IntType,
                runSynthesis store (Op2 (Var (Name "boolean")) Divide (Var (Name "int"))) ~?= UnknownType,
                runSynthesis store (Op2 (Var (Name "int")) Modulo (Var (Name "int"))) ~?= IntType,
                runSynthesis store (Op2 (Var (Name "string")) Modulo (Var (Name "int"))) ~?= UnknownType,
                runSynthesis store (Op2 (Var (Name "int")) Eq (Var (Name "int"))) ~?= BooleanType,
                runSynthesis store (Op2 (Var (Name "int")) Eq (Var (Name "string"))) ~?= UnknownType,
                runSynthesis store (Op2 (Var (Name "string")) Gt (Var (Name "string"))) ~?= BooleanType,
                runSynthesis store (Op2 (Var (Name "string")) Gt (Var (Name "boolean"))) ~?= UnknownType,
                runSynthesis store (Op2 (Var (Name "boolean")) Ge (Var (Name "boolean"))) ~?= BooleanType,
                runSynthesis store (Op2 (Var (Name "boolean")) Ge (Var (Name "int"))) ~?= UnknownType,
                runSynthesis store (Op2 (Var (Name "string")) Lt (Var (Name "string"))) ~?= BooleanType,
                runSynthesis store (Op2 (Var (Name "string")) Lt (Var (Name "int"))) ~?= UnknownType,
                runSynthesis store (Op2 (Var (Name "boolean")) Le (Var (Name "boolean"))) ~?= BooleanType,
                runSynthesis store (Op2 (Var (Name "boolean")) Le (Var (Name "string"))) ~?= UnknownType,
                runSynthesis store (Op2 (Var (Name "string")) Concat (Var (Name "string"))) ~?= StringType,
                runSynthesis store (Op2 (Var (Name "string")) Concat (Var (Name "int"))) ~?= UnknownType
            ]

-- Test synthesis function with TableConst as input
test_synthesisTableConst :: Test
test_synthesisTableConst =
    "synthesis TableConst" ~:
        TestList
            [ 
                runSynthesis store (TableConst [FieldName "x" (Var (Name "int")), FieldName "y" (Var (Name "int"))]) ~?= TableType StringType IntType,
                runSynthesis store (TableConst [FieldName "x" (Var (Name "int")), FieldName "y" (Var (Name "string"))]) ~?= TableType StringType (UnionType IntType StringType),
                runSynthesis store (TableConst [FieldKey (Var (Name "string")) (Var (Name "int")), FieldKey (Var (Name "string")) (Var (Name "int"))]) ~?= TableType StringType IntType,
                runSynthesis store (TableConst [FieldKey (Var (Name "string")) (Var (Name "int")), FieldKey (Var (Name "string")) (Var (Name "string"))]) ~?= TableType StringType (UnionType IntType StringType),
                runSynthesis store (TableConst [FieldKey (Var (Name "string")) (Var (Name "int")), FieldKey (Var (Name "int")) (Var (Name "int"))]) ~?= TableType (UnionType StringType IntType) IntType, 
                runSynthesis store (TableConst [FieldKey (Var (Name "int-or-string")) (Var (Name "int")), FieldKey (Var (Name "string")) (Var (Name "int"))]) ~?= TableType (UnionType IntType StringType) IntType
            ]

-- Test synthesis function with Call as input
test_synthesisCall :: Test
test_synthesisCall =
    "synthesis Call" ~:
        TestList
            [ 
                runSynthesis store (Call (Name "function1") [Var (Name "int"), Var (Name "string")]) ~?= UnknownType,
                runSynthesis store (Call (Name "function1") [Var (Name "String"), Var (Name "string")]) ~?= UnknownType,
                runSynthesis store (Call (Name "function1") [Var (Name "int")]) ~?= StringType,
                runSynthesis store (Call (Name "function4") [Var (Name "int")]) ~?= UnionType IntType StringType,
                runSynthesis store (Call (Name "function4") [Var (Name "string")]) ~?= UnknownType, 
                runSynthesis store (Call (Name "function4") [Var (Name "boolean")]) ~?= UnknownType, 
                runSynthesis store (Call (Name "function4") [Var (Name "int")]) ~?= UnionType IntType StringType, 
                runSynthesis store (Call (Name "function1") []) ~?= UnknownType, 
                runSynthesis store (Call (Name "function1") [Val (IntVal 5), Val (IntVal 4)]) ~?= UnknownType, 
                runSynthesis store (Call (Name "function0") []) ~?= StringType, 
                runSynthesis store (Call (Name "function0") [Val (IntVal 5), Val (IntVal 4)]) ~?= UnknownType, 
                runSynthesis store (Call (Name "function0") [Val NilVal]) ~?= UnknownType 
            ]

test_typeCheckStatement :: Test 
test_typeCheckStatement = 
    "typechecking statement" ~: 
        TestList 
            [
                S.evalState (typeCheckStatement (Assign (Name "f",FunctionType IntType StringType) (Val (FunctionVal [("a",IntType)] StringType (Block [Return (Val (StringVal "here"))]))))) emptyTypeEnv ~?= Right ()
            ]


test :: IO Counts 
test = runTestTT $ TestList [test_typeCheckStatement, test_isSubtype, test_checkerVar, test_checkerVal, test_checkerOp1, test_checkerOp2, test_checkerTableConst, test_checkerCall, test_synthesisVar, test_synthesisVal, test_synthesisOp1, test_synthesisOp2, test_synthesisTableConst, test_synthesisCall]
{-
===================================================================
================== TypeChecker: QuickCheck Tests ==================
===================================================================
-}

-- Quickcheck property for runChecker function
prop_checker :: Expression -> LType -> Bool
prop_checker e t = runChecker store e t == (runSynthesis store e <: t)

-- Quickcheck property for synthesis function
prop_synthesis :: Expression -> Bool
prop_synthesis e = runChecker store e (runSynthesis store e)

qc :: IO ()
qc = do
  putStrLn "synthesis"
  QC.quickCheck prop_synthesis
  putStrLn "checker"
  QC.quickCheck prop_checker