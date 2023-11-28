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

-- | Check if variable holds value in store. 
checkVarValue :: String -> Value -> Store -> Either String Bool 
checkVarValue targetName targetValue s = case Map.lookup globalTableName s of 
    Nothing -> Left "Failed to find global table."
    Just globalTable -> case Map.lookup (StringVal targetName) globalTable of 
        Nothing -> Left ("Failed to find" ++ targetName ++  "variable")
        Just v -> Right $ v == targetValue

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
            "if1" ~: testFile "test/lu/if1.lu" (checkVarValue "result" (IntVal 5))
          ]


