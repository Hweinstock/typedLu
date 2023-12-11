module LuE2ETest where

import Context (Context, ExtendedContext)
import Context qualified as C
import Data.Map qualified as Map
import LuEvaluator (EvalEnv, Store, errorCodeName, eval, exec, globalTableName, haltFlagName, toStore)
import LuEvaluatorTest (initialEnv)
import LuParser (parseLuFile)
import LuSyntax
import LuTypeChecker (TypeEnv, contextLookup, getUncalledFunc, runForEnv, typeCheckAST)
import LuTypes
import State qualified as S
import Test.HUnit (Counts, Test (..), assert, runTestTT, (~:), (~?=))

processFileForStore :: (ExtendedContext env) => String -> (Block -> env -> Either String env) -> IO (Either String env)
processFileForStore fp execBlock = do
  parseResult <- parseLuFile fp
  return $ case parseResult of
    (Left _) -> Left "Failed to parse file"
    (Right ast) -> execBlock ast C.emptyContext

-- | Parse and run file to get resulting Store (or error message)
evalFileForStore :: String -> IO (Either String EvalEnv)
evalFileForStore fp = processFileForStore fp exec

typeCheckFileForStore :: String -> IO (Either String TypeEnv)
typeCheckFileForStore fp = processFileForStore fp runForEnv

checkThrowsError :: String -> String -> IO Bool
checkThrowsError fp err = do
  result <- evalFileForStore fp
  return $ case result of
    Left s -> s == err
    _ -> False

testIOResult :: IO Bool -> IO ()
testIOResult b = b >>= assert

checkVarProperty :: String -> (Value -> Bool) -> EvalEnv -> Either String Bool
checkVarProperty targetName property s = case Map.lookup globalTableName (toStore s) of
  Nothing -> Left "Failed to find global table."
  Just globalTable -> case Map.lookup (StringVal targetName) globalTable of
    Nothing -> Left ("Failed to find" ++ targetName ++ "variable")
    Just v -> Right $ property v

-- | Check if variable holds value in store.
checkVarValueInStore :: String -> Value -> EvalEnv -> Either String Bool
checkVarValueInStore targetName targetValue = checkVarProperty targetName (== targetValue)

-- | Concise way to check multiple variable values.
checkVarValuesInStore :: [(String, Value)] -> EvalEnv -> Either String Bool
checkVarValuesInStore valuePairs s =
  let results = map (\(n, v) -> checkVarValueInStore n v s) valuePairs
   in return $ all didFail results
  where
    didFail :: Either String Bool -> Bool
    didFail (Right True) = True
    didFail _ = False

-- | Check if variable holds value in store.
checkVarExistsInStore :: String -> EvalEnv -> Either String Bool
checkVarExistsInStore targetName = checkVarProperty targetName (const True)

-- | Apply target function to final store of given file.
-- Ex. checkFileOutputStore "test/lu/if1.lu" (checkVarValue "result" (IntVal 5)) ==> Right True
--     since final value of "result" is (IntVal 5).
checkFileOutputStore :: String -> (EvalEnv -> Either String Bool) -> IO (Either String Bool)
checkFileOutputStore fp checkFn = do
  finalState <- evalFileForStore fp
  case finalState of
    (Left _) -> return $ Left "Failed to retrieve store"
    (Right s) -> return $ checkFn s

checkFileTypeStore :: String -> (TypeEnv -> Either String Bool) -> IO (Either String Bool)
checkFileTypeStore fp checkFn = do
  finalStore <- typeCheckFileForStore fp
  case finalStore of
    (Left _) -> return $ Left "Failed to retrieve store"
    (Right s) -> do
      return $ checkFn s

testTypeCheckFile :: String -> Bool -> IO ()
testTypeCheckFile fp flipped = do
  parseResult <- parseLuFile fp
  case parseResult of
    (Left l) -> assert False
    Right ast -> case typeCheckAST ast C.emptyContext of
      (Left l) -> assert (not flipped)
      _ -> assert flipped

getTypeEnvFile :: String -> IO (Either String TypeEnv)
getTypeEnvFile fp = do
  parseResult <- parseLuFile fp
  case parseResult of
    (Left l) -> return $ Left l
    Right ast -> case runForEnv ast C.emptyContext of
      (Left l2) -> return $ Left l2
      Right store -> return $ Right store

seeTypeStore :: String -> IO ()
seeTypeStore fp = do
  r <- getTypeEnvFile fp
  case r of
    Left l -> putStrLn (show l)
    Right r -> putStrLn (show r)

testEvalFile :: String -> (EvalEnv -> Either String Bool) -> IO ()
testEvalFile fp checkFn = do
  res <- checkFileOutputStore fp checkFn
  case res of
    Right True -> assert True
    _ -> assert False

testTypeCheckFileStore :: String -> (TypeEnv -> Either String Bool) -> IO ()
testTypeCheckFileStore fp checkFn = do
  res <- checkFileTypeStore fp checkFn
  case res of
    Right True -> assert True
    _ -> assert False

test_if :: Test
test_if =
  "e2e testing if" ~:
    TestList
      [ "if1" ~: testEvalFile "test/lu/if1.lu" (checkVarValueInStore "result" (IntVal 5)),
        "if2" ~: testEvalFile "test/lu/if2.lu" (checkVarValueInStore "result" (StringVal "hello"))
      ]

test_function :: Test
test_function =
  "e2e function" ~:
    TestList
      [ "function1" ~: testEvalFile "test/lu/function1.lu" (checkVarExistsInStore "foo"),
        "function2" ~: testEvalFile "test/lu/function2.lu" (checkVarValuesInStore [("z", IntVal 11)]),
        "function3" ~: testEvalFile "test/lu/function3.lu" (checkVarValuesInStore [("z", BoolVal False), ("s", StringVal "True"), ("x", IntVal 1), ("y", IntVal 2), ("result", IntVal (-1))]),
        "function4" ~: testEvalFile "test/lu/function4.lu" (checkVarValueInStore "z" (IntVal 5)),
        "function5" ~: testEvalFile "test/lu/function5.lu" (checkVarValuesInStore [("z", StringVal "foo"), ("x", IntVal 1)]),
        "function6" ~: testEvalFile "test/lu/function6.lu" (checkVarValuesInStore [("f", BoolVal False), ("z", IntVal 1)]),
        "recFunction" ~: testEvalFile "test/lu/recFunction.lu" (checkVarValueInStore "z" (IntVal 720)),
        "weirdScopesFunc" ~: testEvalFile "test/lu/weirdScopesFunc.lu" (checkVarValuesInStore [("result", IntVal 18), ("result2", IntVal 12)]),
        "unionTypeFunc" ~: testEvalFile "test/lu/unionTypeFunc.lu" (checkVarExistsInStore "foo"),
        "function7" ~: testEvalFile "test/lu/function7.lu" (checkVarValuesInStore [("b", IntVal 10), ("z", IntVal 8)]),
        "nameShadow" ~: testEvalFile "test/lu/nameShadow.lu" (checkVarValuesInStore [("res", IntVal 10), ("s", StringVal "s")])
      ]

test_typeSig :: Test
test_typeSig =
  "e2e typeSig" ~:
    TestList
      [ "optionalSig1" ~: testEvalFile "test/lu/optionalSig1.lu" (checkVarValuesInStore [("x", IntVal 5), ("x2", IntVal 5), ("s", StringVal "hello"), ("s2", StringVal "hello"), ("z", BoolVal True), ("z2", BoolVal True)]),
        "optionalSig2" ~: testEvalFile "test/lu/optionalSig2.lu" (checkVarExistsInStore "f" >> checkVarExistsInStore "u")
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
        "unionReturn" ~: testTypeCheckFile "test/lu/unionReturn.lu" False
      ]

test_typeCheckStore :: Test
test_typeCheckStore =
  "tesing type checker store" ~:
    TestList
      [ "uncalledFunc" ~: testTypeCheckFileStore "test/lu/uncalledFunc.lu" (containsFunc "foo"),
        "uncalledFunc" ~: testTypeCheckFileStore "test/lu/uncalledFunc.lu" (isNilOrUndefined "z" False),
        "calledFunc" ~: testTypeCheckFileStore "test/lu/calledFunc.lu" (isNilOrUndefined "z" True)
      ]
  where
    containsFunc :: Name -> TypeEnv -> Either String Bool
    containsFunc n env = case getUncalledFunc env n of
      Just _ -> return True
      _ -> Left "Failed to find"

    isNilOrUndefined :: Name -> Bool -> TypeEnv -> Either String Bool
    isNilOrUndefined n expected env = case S.evalState (contextLookup n) env of
      NilType -> return expected
      UnknownType -> return expected
      _ -> return (not expected)

test_error :: Test
test_error =
  "e2e error" ~:
    TestList
      [ "IllegalArguments1" ~: testIOResult $ checkThrowsError "test/lu/error1.lu" (show IllegalArguments),
        "DivideByZero" ~: testIOResult $ checkThrowsError "test/lu/error2.lu" (show DivideByZero)
      ]

test :: IO Counts
test = runTestTT $ TestList [test_if, test_function, test_typeSig, test_error]
