{-# LANGUAGE FunctionalDependencies #-}

module LuE2ETest where

import Context (Context, Environment, Reference (GlobalRef))
import Context qualified as C
import Control.Monad.State qualified as State
import Data.Either (isLeft)
import Data.Map qualified as Map
import Data.Maybe (isJust)
import LuEvaluator (EvalEnv, Store, errorCodeName, eval, exec, globalTableName, haltFlagName, toStore)
import LuEvaluatorTest (initialEnv)
import LuParser (parseLuFile)
import LuSyntax
import LuTypeChecker (TypeEnv, execEnv, getUncalledFunc, typeCheckAST)
import LuTypes
import Test.HUnit (Assertion, Counts, Test (..), assert, runTestTT, (~:), (~?=))

class (Environment env v) => TestableEnvironment env v | env -> v where
  execBlock :: Block -> env -> Either String env

  runFileForStore :: String -> IO (Either String env)
  runFileForStore fp = do
    parseResult <- parseLuFile fp
    return $ case parseResult of
      (Left _) -> Left "Failed to parse file"
      (Right ast) -> execBlock ast C.emptyEnv

  checkOutputStore :: String -> (env -> Bool) -> IO Bool
  checkOutputStore fp checkFn = do
    finalState <- runFileForStore fp
    case finalState of
      (Left _) -> return False
      (Right s) -> return $ checkFn s

  testFile :: String -> (env -> Bool) -> IO Assertion
  testFile fp checkFn = assert <$> checkOutputStore fp checkFn

instance TestableEnvironment EvalEnv Value where
  execBlock :: Block -> EvalEnv -> Either String EvalEnv
  execBlock = exec

instance TestableEnvironment TypeEnv LType where
  execBlock :: Block -> TypeEnv -> Either String TypeEnv
  execBlock = execEnv

testTypeCheckFile :: String -> Bool -> IO Assertion
testTypeCheckFile fp expected = do
  (res :: Either String TypeEnv) <- runFileForStore fp
  case res of
    Left _ -> return $ assert (not expected)
    Right _ -> return $ assert expected

-- | assert that eval of file throws certain error
checkEvalThrowsError :: String -> String -> IO ()
checkEvalThrowsError fp err = do
  (result :: Either String EvalEnv) <- runFileForStore fp
  case result of
    Left s -> assert $ s == err
    _ -> assert False

testIOResult :: IO Bool -> IO ()
testIOResult b = b >>= assert

-- | Check property of variable in env.
checkVarProperty :: String -> (Value -> Bool) -> EvalEnv -> Bool
checkVarProperty targetName property env = property $ snd $ State.evalState (C.resolveName targetName) env

-- | Check if variable holds target value in store.
checkVarValueInStore :: String -> Value -> EvalEnv -> Bool
checkVarValueInStore targetName targetValue = checkVarProperty targetName (== targetValue)

-- | Check if variable holds any value in store.
checkVarExistsInStore :: String -> EvalEnv -> Bool
checkVarExistsInStore targetName = checkVarProperty targetName (/= NilVal)

-- | Concise way to check multiple variable values.
checkVarValuesInStore :: [(String, Value)] -> EvalEnv -> Bool
checkVarValuesInStore valuePairs env = all (\(n, v) -> checkVarValueInStore n v env) valuePairs

-- Run Typechecker and print the result.
seeTypeEnv :: String -> IO ()
seeTypeEnv fp = do
  (r :: Either String TypeEnv) <- runFileForStore fp
  case r of
    Left l -> putStrLn ("Error: \n" ++ show r)
    Right r -> putStrLn ("Successfully type-checked with store: \n" ++ show r)

seeEvalEnv :: String -> IO ()
seeEvalEnv fp = do
  (r :: Either String EvalEnv) <- runFileForStore fp
  case r of
    Left l -> putStrLn ("Error: " ++ show r)
    Right r -> putStrLn ("Successfully evaluated with store: " ++ show r)

test_if :: Test
test_if =
  "e2e testing if" ~:
    TestList
      [ "if1" ~: testFile "test/lu/if1.lu" (checkVarValueInStore "result" (IntVal 5)),
        "if2" ~: testFile "test/lu/if2.lu" (checkVarValueInStore "result" (StringVal "hello"))
      ]

test_function :: Test
test_function =
  "eval function" ~:
    TestList
      [ "function1" ~: testFile "test/lu/function1.lu" (checkVarExistsInStore "foo"),
        "function2" ~: testFile "test/lu/function2.lu" (checkVarValuesInStore [("z", IntVal 11)]),
        "function3" ~: testFile "test/lu/function3.lu" (checkVarValuesInStore [("z", BoolVal False), ("s", StringVal "True"), ("x", IntVal 1), ("y", IntVal 2), ("result", IntVal (-1))]),
        "function4" ~: testFile "test/lu/function4.lu" (checkVarValueInStore "z" (IntVal 5)),
        "function5" ~: testFile "test/lu/function5.lu" (checkVarValuesInStore [("z", StringVal "foo"), ("x", IntVal 1)]),
        "function6" ~: testFile "test/lu/function6.lu" (checkVarValuesInStore [("f", BoolVal False), ("z", IntVal 1)]),
        "recFunction" ~: testFile "test/lu/recFunction.lu" (checkVarValueInStore "z" (IntVal 720)),
        "recFunction2" ~: testFile "test/lu/recFunction2.lu" (checkVarValuesInStore [("result", IntVal 55)]),
        "weirdScopesFunc" ~: testFile "test/lu/weirdScopesFunc.lu" (checkVarValuesInStore [("result", IntVal 18), ("result2", IntVal 12)]),
        "unionTypeFunc" ~: testFile "test/lu/unionTypeFunc.lu" (checkVarExistsInStore "foo"),
        "function7" ~: testFile "test/lu/function7.lu" (checkVarValuesInStore [("b", IntVal 10), ("z", IntVal 8)]),
        "nameShadow" ~: testFile "test/lu/nameShadow.lu" (checkVarValuesInStore [("res", IntVal 10), ("s", StringVal "s")]),
        "mutualRecFunction" ~: testFile "test/lu/mutualRecFunc.lu" (checkVarValuesInStore [("result", BoolVal True), ("result2", BoolVal True)])
        -- "functionFromTable" ~: testFile "test/lu/functionFromTable.lu" (checkVarValuesInStore [("result", IntVal 6)])
      ]

test_typeSig :: Test
test_typeSig =
  "e2e typeSig" ~:
    TestList
      [ "optionalSig1" ~: testFile "test/lu/optionalSig1.lu" (checkVarValuesInStore [("x", IntVal 5), ("x2", IntVal 5), ("s", StringVal "hello"), ("s2", StringVal "hello"), ("z", BoolVal True), ("z2", BoolVal True)]),
        "optionalSig2" ~: testFile "test/lu/optionalSig2.lu" (checkVarExistsInStore "f" >> checkVarExistsInStore "u")
      ]

test_typeCheck :: Test
test_typeCheck =
  "testing type checker" ~:
    TestList
      [ "abs" ~: testTypeCheckFile "test/lu/abs.lu" True,
        "exp" ~: testTypeCheckFile "test/lu/exp.lu" False,
        "fact" ~: testTypeCheckFile "test/lu/fact.lu" True,
        "repeat" ~: testTypeCheckFile "test/lu/repeat.lu" True,
        "table" ~: testTypeCheckFile "test/lu/table.lu" False,
        "test" ~: testTypeCheckFile "test/lu/test.lu" True,
        "bfs" ~: testTypeCheckFile "test/lu/bfs.lu" False,
        "times" ~: testTypeCheckFile "test/lu/times.lu" True,
        "optionalSig1" ~: testTypeCheckFile "test/lu/optionalSig1.lu" True,
        "optionalSig2" ~: testTypeCheckFile "test/lu/optionalSig2.lu" True,
        "recFunction" ~: testTypeCheckFile "test/lu/recFunction.lu" True,
        "recFunction2" ~: testTypeCheckFile "test/lu/recFunction2.lu" True,
        "function1" ~: testTypeCheckFile "test/lu/function1.lu" True,
        "function2" ~: testTypeCheckFile "test/lu/function2.lu" True,
        "function3" ~: testTypeCheckFile "test/lu/function3.lu" True,
        "function4" ~: testTypeCheckFile "test/lu/function4.lu" True,
        "function5" ~: testTypeCheckFile "test/lu/function5.lu" True,
        "function6" ~: testTypeCheckFile "test/lu/function6.lu" True,
        "function7" ~: testTypeCheckFile "test/lu/function7.lu" True,
        "function8" ~: testTypeCheckFile "test/lu/function8.lu" True,
        "unionTypeFunc" ~: testTypeCheckFile "test/lu/unionTypeFunc.lu" False,
        "weirdScopesFunc" ~: testTypeCheckFile "test/lu/weirdScopesFunc.lu" True,
        "nestedGlobal" ~: testTypeCheckFile "test/lu/nestedGlobal.lu" False,
        "nestedGlobal2" ~: testTypeCheckFile "test/lu/nestedGlobal2.lu" True,
        "nestedFuncReturnTypeGood" ~: testTypeCheckFile "test/lu/nestedFuncReturnTypeGood.lu" True,
        "nestedFuncReturnTypeBad" ~: testTypeCheckFile "test/lu/nestedFuncReturnTypeBad.lu" False,
        "nestedFuncReturnTypeBad2" ~: testTypeCheckFile "test/lu/nestedFuncReturnTypeBad2.lu" False,
        "nameShadow" ~: testTypeCheckFile "test/lu/nameShadow.lu" True,
        "nameShadowBad" ~: testTypeCheckFile "test/lu/nameShadowBad.lu" False,
        "unionReturn" ~: testTypeCheckFile "test/lu/unionReturn.lu" False,
        "unionReturn2" ~: testTypeCheckFile "test/lu/unionReturn2.lu" True,
        "missingReturn" ~: testTypeCheckFile "test/lu/missingReturn.lu" False,
        "mutualRec" ~: testTypeCheckFile "test/lu/mutualRecFunc.lu" True,
        "redefine" ~: testTypeCheckFile "test/lu/redefine.lu" False,
        "tables1" ~: testTypeCheckFile "test/lu/tables1.lu" True,
        "typedBFS" ~: testTypeCheckFile "test/lu/typedBFS.lu" True
      ]

test_typeCheckStore :: Test
test_typeCheckStore =
  "tesing type checker store" ~:
    TestList
      [ "uncalledFunc" ~: testFile "test/lu/uncalledFunc.lu" (containsFunc "foo"),
        "uncalledFunc" ~: testFile "test/lu/uncalledFunc.lu" (isNilOrUndefined "z" False),
        "calledFunc" ~: testFile "test/lu/calledFunc.lu" (isNilOrUndefined "z" True)
      ]
  where
    containsFunc :: Name -> TypeEnv -> Bool
    containsFunc n env = isJust $ getUncalledFunc env (GlobalRef n)

    isNilOrUndefined :: Name -> Bool -> TypeEnv -> Bool
    isNilOrUndefined n expected env = expected == (actual == NilType || actual == UnknownType)
      where
        actual = snd $ State.evalState (C.resolveName n) env

test_error :: Test
test_error =
  "e2e error" ~:
    TestList
      [ "IllegalArguments1" ~: checkEvalThrowsError "test/lu/error1.lu" (show IllegalArguments),
        "DivideByZero" ~: checkEvalThrowsError "test/lu/error2.lu" (show DivideByZero)
      ]

test :: IO Counts
test = runTestTT $ TestList [test_if, test_function, test_typeSig, test_error, test_typeCheck]
