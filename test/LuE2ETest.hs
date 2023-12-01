module LuE2ETest where 

import Test.HUnit (Counts, Test (..), runTestTT, (~:), (~?=), assert)
import LuParser (parseLuFile)
import LuEvaluator (Store, eval, initialStore, resolveVar, index, globalTableName)
import LuSyntax
import State qualified as S
import Data.Map qualified as Map

-- | Parse and run file to get resulting Store (or error message)
runFileForStore :: String -> IO (Either String Store)
runFileForStore fp = do
    parseResult <- parseLuFile fp
    case parseResult of 
        (Left _) -> do 
            return $ Left "Failed to parse file"
        (Right ast) -> do 
            let finalState = S.execState (eval ast) initialStore
            return $ Right finalState

checkVarProperty :: String -> (Value -> Bool) -> Store -> Either String Bool 
checkVarProperty targetName property s = case Map.lookup globalTableName s of 
    Nothing -> Left "Failed to find global table."
    Just globalTable -> case Map.lookup (StringVal targetName) globalTable of 
        Nothing -> Left ("Failed to find" ++ targetName ++  "variable")
        Just v -> Right $ property v

-- | Check if variable holds value in store. 
checkVarValueInStore :: String -> Value -> Store -> Either String Bool 
checkVarValueInStore targetName targetValue = checkVarProperty targetName (== targetValue)

-- | Concise way to check multiple variable values.
checkVarValuesInStore :: [(String, Value)] -> Store -> Either String Bool 
checkVarValuesInStore valuePairs s = let results = map (\(n, v) -> checkVarValueInStore n v s) valuePairs in 
    return $ all didFail results 
    where 
        didFail :: Either String Bool -> Bool
        didFail (Right True) = True 
        didFail _ = False
        
-- | Check if variable holds value in store. 
checkVarExistsInStore :: String -> Store -> Either String Bool 
checkVarExistsInStore targetName = checkVarProperty targetName (const True)

-- | Apply target function to final store of given file. 
-- Ex. checkFileOutputStore "test/lu/if1.lu" (checkVarValue "result" (IntVal 5)) ==> Right True
--     since final value of "result" is (IntVal 5).    
checkFileOutputStore :: String -> (Store -> Either String Bool) -> IO (Either String Bool)
checkFileOutputStore fp checkFn = do 
    finalState <- runFileForStore fp 
    case finalState of 
        (Left _) -> return $ Left "Failed to retrieve store"
        (Right s) -> return $ checkFn s

testFile :: String -> (Store -> Either String Bool) -> IO () 
testFile fp checkFn = do 
    res <- checkFileOutputStore fp checkFn
    case res of 
        Right True -> assert True 
        _ -> assert False

test_if :: Test 
test_if = 
    "e2e testing if" ~:
        TestList 
          [
            "if1" ~: testFile "test/lu/if1.lu" (checkVarValueInStore "result" (IntVal 5)), 
            "if2" ~: testFile "test/lu/if2.lu" (checkVarValueInStore "result" (StringVal "hello"))
          ]


test_function :: Test 
test_function = 
    "e2e function" ~: 
        TestList 
           [
             "function1" ~: testFile "test/lu/function1.lu" (checkVarExistsInStore "foo"), 
             "function2" ~: testFile "test/lu/function2.lu" (checkVarValuesInStore [("z", IntVal 11), ("x1", NilVal), ("y1", NilVal)]), 
             "function3" ~: testFile "test/lu/function3.lu" (checkVarValuesInStore [("z", IntVal (-1)), ("s", StringVal "True"), ("x", IntVal 1), ("y", IntVal 2)]), 
             "function4" ~: testFile "test/lu/function4.lu" (checkVarValueInStore "z" (IntVal 5)), 
             "function5" ~: testFile "test/lu/function5.lu" (checkVarValuesInStore [("z", StringVal "foo"), ("x", IntVal 1)]), 
             "function6" ~: testFile "test/lu/function6.lu" (checkVarValuesInStore [("f", BoolVal False), ("z", IntVal 1)]), 
             "recFunction" ~: testFile "test/lu/recFunction.lu" (checkVarValueInStore "z" (IntVal 720)), 
             "weirdScopesFunc" ~: testFile "test/lu/weirdScopesFunc.lu" (checkVarValuesInStore [("result", IntVal 18), ("result2", IntVal 12)]), 
             "unionTypeFunc" ~: testFile "test/lu/unionTypeFunc.lu" (checkVarExistsInStore "foo"), 
             "function7" ~: testFile "test/lu/function7.lu" (checkVarValuesInStore [("b", IntVal 10), ("z", IntVal 8)])
           ]

test :: IO Counts 
test = runTestTT $ TestList [test_if, test_function]