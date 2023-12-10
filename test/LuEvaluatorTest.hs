module LuEvaluatorTest where 

import LuSyntax
import LuEvaluator
import State qualified as S
import Test.HUnit (Counts, Test (..), runTestTT, (~:), (~?=))
import Data.Map (Map, (!?))
import Data.Map qualified as Map
import Test.QuickCheck qualified as QC

test_index :: Test
test_index =
  "index tests" ~:
    TestList
      [ -- The global variable "x" is unitialized (i.e. not present in the initial store)
        S.evalState (index xref) initialEnv ~?= NilVal,
        -- But there is a value for "x" available in the extended store
        S.evalState (index xref) extendedEnv ~?= IntVal 3,
        -- If a table name is not found in the store, accessing its reference also returns nil.
        S.evalState (index yref) initialEnv ~?= NilVal,
        -- We should also be able to access "t[1]" in the extended store
        S.evalState (index yref) extendedEnv ~?= BoolVal True,
        S.evalState (index (TableRef "z" NilVal)) extendedEnv ~?= NilVal,
        -- Updates using the `nil` key are ignored
        toStore (S.execState (update (TableRef "_t" NilVal) (IntVal 3)) extendedEnv) ~?= toStore extendedEnv,
        S.evalState (index (GlobalRef "t")) extendedEnv ~?= TableVal "_t1"
      ]

test_update :: Test
test_update =
  "index tests" ~:
    TestList
      [ -- If we assign to x, then we can find its new value
        S.evalState (update xref (IntVal 4) >> index xref) initialEnv ~?= IntVal 4,
        -- If we assign to x, then remove it, we cannot find it anymore
        S.evalState (update xref (IntVal 4) >> update xref NilVal >> index xref) initialEnv ~?= NilVal,
        -- If we assign to t.y, then we can find its new value
        S.evalState (update yref (IntVal 5) >> index yref) extendedEnv ~?= IntVal 5,
        -- If we assign nil to t.y, then we cannot find it
        S.evalState (update yref NilVal >> index yref) extendedEnv ~?= NilVal
      ]

test_resolveVar :: Test
test_resolveVar =
  "resolveVar" ~:
    TestList
      [ -- we should be able to resolve global variable `x` in the initial store, even though it is not defined
        S.evalState (resolveVar (Name "x")) initialEnv ~?= Just (GlobalRef "x") ,
        S.evalState (resolveVar (Name "x")) extendedEnv ~?= Just (GlobalRef "x"),
        -- But in the case of Dot or Proj, the first argument should evaluate to a
        -- TableVal that is defined in the store. If it does not, then resolveVar
        -- should return Nothing.
        S.evalState (resolveVar (Dot (Val NilVal) "x")) initialEnv ~?= Nothing,
        S.evalState (resolveVar (Dot (Var (Name "t")) "x")) initialEnv ~?= Nothing,
        -- For Proj we also shouldn't project from Nil
        S.evalState (resolveVar (Proj (Var (Name "t")) (Val NilVal))) extendedEnv ~?= Nothing,
        -- If the table is defined, we should return a reference to it, even when the field is undefined
        S.evalState (resolveVar (Dot (Var (Name "t")) "z")) extendedEnv ~?= Just (TableRef "_t1" (StringVal "z")),
        S.evalState (resolveVar (Dot (Var (Name "t")) "y")) extendedEnv ~?= Just (TableRef "_t1" (StringVal "y")),
        S.evalState (resolveVar (Dot (Var (Name "t2")) "z")) extendedEnv ~?= Nothing,
        -- and how we refer to the field shouldn't matter
        S.evalState (resolveVar (Proj (Var (Name "t")) (Val (StringVal "z")))) extendedEnv ~?= Just (TableRef "_t1" (StringVal "z")),
        S.evalState (resolveVar (Proj (Var (Name "t2")) (Val (StringVal "z")))) extendedEnv ~?= Nothing,
        S.evalState (resolveVar (Proj (Val NilVal) (Val (StringVal "z")))) extendedEnv ~?= Nothing
      ]

test_evaluateNot :: Test
test_evaluateNot =
  "evaluate not" ~:
    TestList
      [ evaluate (Op1 Not (Val NilVal)) initialEnv ~?= BoolVal True,
        evaluate (Op1 Not (Val (IntVal 3))) initialEnv ~?= BoolVal False
      ]

test_evaluateLen :: Test
test_evaluateLen =
  "evaluate len" ~:
    TestList
      [ evaluate (Op1 Len (Val (StringVal "5520"))) extendedEnv ~?= IntVal 4,
        evaluate (Op1 Len (Val (TableVal "_G"))) extendedEnv ~?= IntVal 2,
        evaluate (Op1 Len (Val (TableVal "_t1"))) extendedEnv ~?= IntVal 2,
        evaluate (Op1 Len (Val (TableVal "_t550"))) extendedEnv ~?= NilVal,
        evaluate (Op1 Len (Val (IntVal 5520))) extendedEnv ~?= IntVal 5520,
        evaluate (Op1 Len (Val (BoolVal True))) extendedEnv ~?= IntVal 1
      ]

test_tableConst :: Test
test_tableConst =
  "evaluate { x = 3 } " ~:
    TestList
      [ toStore (S.execState
          (evalE (TableConst [FieldName "x" (Val (IntVal 3))]))
          initialEnv)
          ~?= Map.fromList
                  [ ("_G", Map.empty),
                    ("_t1", Map.fromList [(StringVal "x", IntVal 3)])
                  ],
        toStore (S.execState
          (evalE (TableConst [FieldName "x" (Val (IntVal 3)), FieldName "y" (Val (IntVal 5))]))
          initialEnv)
          ~?= Map.fromList
                  [ ("_G", Map.empty),
                    ("_t1", Map.fromList [(StringVal "x", IntVal 3), (StringVal "y", IntVal 5)])
                  ],
        toStore (S.execState
          (evalE (TableConst [FieldKey (Val (StringVal "x")) (Val (IntVal 3))]))
          initialEnv)
          ~?= Map.fromList
                  [ ("_G", Map.empty),
                    ("_t1", Map.fromList [(StringVal "x", IntVal 3)])
                  ],
        toStore (S.execState
          (evalE (TableConst [FieldKey (Val (StringVal "x")) (Val (IntVal 3)), FieldName "y" (Val (IntVal 5))]))
          initialEnv)
          ~?= Map.fromList
                  [ ("_G", Map.empty),
                    ("_t1", Map.fromList [(StringVal "x", IntVal 3), (StringVal "y", IntVal 5)])
                  ],
        toStore (S.execState
          (evalE (TableConst []))
          initialEnv)
          ~?= Map.fromList
                  [ ("_G", Map.empty),
                    ("_t1", Map.empty)
                  ]
      ]

test_evalOp2 :: Test
test_evalOp2 =
  "evaluate Op2" ~:
    TestList
      [ evaluate (Op2 (Val (IntVal 3)) Plus (Val (IntVal 1))) initialEnv ~?= IntVal 4,
        evaluate (Op2 (Val (IntVal 3)) Minus (Val (IntVal 1))) initialEnv ~?= IntVal 2,
        evaluate (Op2 (Val (IntVal 3)) Times (Val (IntVal 1))) initialEnv ~?= IntVal 3,
        evaluate (Op2 (Val (IntVal 4)) Divide (Val (IntVal 2))) initialEnv ~?= IntVal 2,
        evaluate (Op2 (Val (IntVal 3)) Modulo (Val (IntVal 2))) initialEnv ~?= IntVal 1,
        evaluate (Op2 (Val (IntVal 3)) Eq (Val (IntVal 2))) initialEnv ~?= BoolVal False,
        evaluate (Op2 (Val (IntVal 3)) Eq (Val (IntVal 3))) initialEnv ~?= BoolVal True,
        evaluate (Op2 (Val (IntVal 3)) Gt (Val (IntVal 2))) initialEnv ~?= BoolVal True,
        evaluate (Op2 (Val (IntVal 3)) Gt (Val (IntVal 3))) initialEnv ~?= BoolVal False,
        evaluate (Op2 (Val (IntVal 3)) Gt (Val (IntVal 4))) initialEnv ~?= BoolVal False,
        evaluate (Op2 (Val (IntVal 3)) Ge (Val (IntVal 3))) initialEnv ~?= BoolVal True,
        evaluate (Op2 (Val (IntVal 3)) Ge (Val (IntVal 2))) initialEnv ~?= BoolVal True,
        evaluate (Op2 (Val (IntVal 3)) Ge (Val (IntVal 4))) initialEnv ~?= BoolVal False,
        evaluate (Op2 (Val (IntVal 3)) Lt (Val (IntVal 2))) initialEnv ~?= BoolVal False,
        evaluate (Op2 (Val (IntVal 3)) Lt (Val (IntVal 3))) initialEnv ~?= BoolVal False,
        evaluate (Op2 (Val (IntVal 3)) Lt (Val (IntVal 4))) initialEnv ~?= BoolVal True,
        evaluate (Op2 (Val (IntVal 3)) Le (Val (IntVal 3))) initialEnv ~?= BoolVal True,
        evaluate (Op2 (Val (IntVal 3)) Le (Val (IntVal 2))) initialEnv ~?= BoolVal False,
        evaluate (Op2 (Val (IntVal 3)) Ge (Val (IntVal 3))) initialEnv ~?= BoolVal True,
        evaluate (Op2 (Val (IntVal 3)) Ge (Val (IntVal 2))) initialEnv ~?= BoolVal True,
        evaluate (Op2 (Val (IntVal 3)) Ge (Val (IntVal 4))) initialEnv ~?= BoolVal False,
        evaluate (Op2 (Val (IntVal 3)) Ge (Val (IntVal 3))) initialEnv ~?= BoolVal True,
        evaluate (Op2 (Val (IntVal 3)) Ge (Val (IntVal 2))) initialEnv ~?= BoolVal True,
        evaluate (Op2 (Val (StringVal "hello ")) Concat (Val (StringVal "world!"))) initialEnv ~?= StringVal "hello world!"
      ]

test_error :: Test 
test_error = 
  "evaluating errors" ~:
    TestList 
    [
      evaluate (Op2 (Val (IntVal 3)) Plus (Val (StringVal "here"))) initialEnv ~?= ErrorVal IllegalArguments, 
      evaluate (Op2 (Val (IntVal 3)) Plus (Val (BoolVal True))) initialEnv ~?= ErrorVal IllegalArguments, 
      evaluate (Op2 (Val (IntVal 10)) Plus (Val NilVal)) initialEnv ~?= ErrorVal IllegalArguments, 
      evaluate (Op2 (Val (BoolVal True)) Concat (Val NilVal)) initialEnv ~?= ErrorVal IllegalArguments, 
      evaluate (Op2 (Val (IntVal 10)) Times (Val (StringVal "here"))) initialEnv ~?= ErrorVal IllegalArguments, 
      evaluate (Op2 (Val (BoolVal True)) Divide (Val NilVal)) initialEnv ~?= ErrorVal IllegalArguments, 
      evaluate (Op2 (Val (IntVal 10)) Divide (Val (IntVal 0))) initialEnv ~?= ErrorVal DivideByZero, 
      evaluate (Op2 (Val (IntVal 10)) Divide (Op2 (Val (IntVal 5)) Minus (Val (IntVal 5)))) initialEnv ~?= ErrorVal DivideByZero
    ]

tExecTest :: Test
tExecTest =
  "exec wTest" ~:
    toStore (exec wTest initialEnv)
      ~?= Map.fromList [(globalTableName, Map.fromList [(StringVal "x", IntVal 0), (StringVal "y", IntVal 10)])]

tExecFact :: Test
tExecFact =
  "exec wFact" ~:
    toStore (exec wFact initialEnv)
      ~?= Map.fromList
        [ ( globalTableName,
            Map.fromList
              [ (StringVal "f", IntVal 120),
                (StringVal "n", IntVal 0),
                (StringVal "x", IntVal 1),
                (StringVal "z", IntVal 120)
              ]
          )
        ]

tExecAbs :: Test
tExecAbs =
  "exec wAbs" ~:
    toStore (exec wAbs initialEnv)
      ~?= Map.fromList
        [ ( globalTableName,
            Map.fromList [(StringVal "x", IntVal 3)]
          )
        ]

tExecTimes :: Test
tExecTimes =
  "exec wTimes" ~:
    toStore (exec wTimes initialEnv)
      ~?= Map.fromList
        [ ( globalTableName,
            Map.fromList [(StringVal "x", IntVal 0), (StringVal "y", IntVal 3), (StringVal "z", IntVal 30)]
          )
        ]

tExecTable :: Test
tExecTable =
  "exec wTable" ~:
    toStore (exec wTable initialEnv)
      ~?= Map.fromList
        [ ( globalTableName,
            Map.fromList
              [ (StringVal "a", TableVal "_t1"),
                (StringVal "k", IntVal 20),
                (StringVal "o1", IntVal 10),
                (StringVal "o2", StringVal "great"),
                (StringVal "o3", IntVal 11)
              ]
          ),
          ("_t1", Map.fromList [(IntVal 20, StringVal "great"), (StringVal "x", IntVal 11)])
        ]

tExecBfs :: Test
tExecBfs = "exec wBfs" ~: TestList [global !? StringVal "found" ~?= Just (BoolVal True)]
  where
    ss = toStore (exec wBfs initialEnv)
    global = case ss !? globalTableName of
      Just g -> g
      Nothing -> Map.empty

test :: IO Counts
test = runTestTT $ TestList [test_error, test_index, test_update, test_resolveVar, test_evaluateNot, test_evaluateLen, test_tableConst, test_evalOp2, tExecTest, tExecAbs, tExecTimes, tExecTable, tExecBfs, tExecFact]

prop_evalE_total :: Expression -> Store -> Bool
prop_evalE_total e s = case evaluate e (fromStore s) of
  NilVal -> True
  IntVal i -> i `seq` True
  BoolVal b -> b `seq` True
  StringVal s -> s `seq` True
  TableVal n -> n `seq` True
  FunctionVal ps rt b -> ps `seq` rt `seq` b `seq` True
  ErrorVal _ -> True -- We don't generate these, so this won't be hit. 

qc :: IO ()
qc = do
  putStrLn "evalE_total"
  quickCheckN 100 prop_evalE_total
