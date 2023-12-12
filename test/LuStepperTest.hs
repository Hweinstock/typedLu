module LuStepperTest where 

import LuSyntax
import LuStepper
import LuEvaluator (EvalEnv, globalTableName, execWithoutError, toStore, Store, fromStore)
import LuEvaluatorTest (initialEnv, extendedEnv)
import State (State)
import State qualified as S
import Data.Map (Map, (!?))
import Data.Map qualified as Map
import Test.QuickCheck qualified as QC
import Test.HUnit (Counts, Test (..), runTestTT, (~:), (~?=))

-- | test.lu:  arithemetic and while loops
tExecStepTest :: Test
tExecStepTest =
  "execStep wTest" ~:
    toStore (execStep wTest initialEnv)
      ~?= Map.fromList
        [ ( globalTableName,
            Map.fromList [(StringVal "x", IntVal 0), (StringVal "y", IntVal 10)]
          )
        ]

-- | abs.lu: absolute value of -3
tExecStepAbs :: Test
tExecStepAbs =
  "execStep wAbs" ~:
    toStore (execStep wAbs initialEnv)
      ~?= Map.fromList [(globalTableName, Map.fromList [(StringVal "x", IntVal 3)])]

-- | times.lu: multiplication of 3 * 10 by repeated addition
tExecStepTimes :: Test
tExecStepTimes =
  "execStep wTimes" ~:
    toStore (execStep wTimes initialEnv)
      ~?= Map.fromList
        [ ( globalTableName,
            Map.fromList [(StringVal "x", IntVal 0), (StringVal "y", IntVal 3), (StringVal "z", IntVal 30)]
          )
        ]

-- | fact.lu:  implementation of factorial function (called with argument 5)
tExecStepFact :: Test
tExecStepFact =
  "execStep wFact" ~:
    toStore (execStep wFact initialEnv)
      ~?= Map.fromList
        [ ( globalTableName,
            Map.fromList [(StringVal "f", IntVal 120), (StringVal "n", IntVal 0), (StringVal "x", IntVal 1), (StringVal "z", IntVal 120)]
          )
        ]

-- | table.lu: examples of accessing data from tables
tExecStepTable :: Test
tExecStepTable =
  "execStep wTable" ~:
    toStore (execStep wTable initialEnv)
      ~?= Map.fromList
        [ ( globalTableName,
            Map.fromList
              [ (StringVal "a", TableVal "_t0"),
                (StringVal "k", IntVal 20),
                (StringVal "o1", IntVal 10),
                (StringVal "o2", StringVal "great"),
                (StringVal "o3", IntVal 11)
              ]
          ),
          ("_t0", Map.fromList [(IntVal 20, StringVal "great"), (StringVal "x", IntVal 11)])
        ]

-- | bfs.lu: calculate breadth-first search of a graph represented by adjacency lists.
-- Search for a path from node 1 to node 10
tExecStepBfs :: Test
tExecStepBfs =
  "execStep wBfs" ~:
    TestList
      [ global !? StringVal "found" ~?= Just (BoolVal True)
      ]
  where
    ss = toStore (execStep wBfs initialEnv)
    global = case ss !? globalTableName of
      Just g -> g
      Nothing -> Map.empty

test_step_with_errors :: Test 
test_step_with_errors = 
  "exec with errors" ~: 
    TestList 
      [
        toStore (execWithoutError b initialEnv) ~?= toStore (S.execState (boundedStep 100 b) initialEnv)
      ]
      where 
          b = Block [If (Op1 Neg (Var (Name "x"))) (Block []) (Block []),If (TableConst []) (Block []) (Block [])]

test :: IO Counts
test = runTestTT $ TestList [test_step_with_errors, tExecStepFact, tExecStepAbs, tExecStepTimes, tExecStepAbs, tExecStepTable, tExecStepBfs]

prop_stepExec :: Block -> QC.Property
prop_stepExec b =
  not (final b) QC.==> final b1 QC.==> toStore m1 == toStore m2
  where
    (b1, m1) = S.runState (boundedStep 100 b) initialEnv
    m2 = execWithoutError b initialEnv

-- | Make sure that we can step every block in every store
prop_step_total :: Block -> Store -> Bool
prop_step_total b s = case S.runState (step b) (fromStore s) of
  (b', s') -> True

qc :: IO () 
qc = do 
    putStrLn "stepExec"
    quickCheckN 100 prop_stepExec
    putStrLn "step_total"
    quickCheckN 100 prop_step_total
