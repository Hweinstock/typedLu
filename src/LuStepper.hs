module LuStepper where

import System.IO
import LuSyntax
import LuParser qualified
import LuEvaluator
import Data.Maybe (fromMaybe)
import Text.Read (readMaybe)
import Data.List qualified as List
import State (State)
import State qualified as S
import Context qualified as C
import Data.Map (Map, (!?))
import Data.Map qualified as Map
import Test.HUnit (Counts, Test (..), runTestTT, (~:), (~?=))
import Test.QuickCheck qualified as QC

step :: Block -> State EvalEnv Block
step b@(Block []) = return b
step b@(Block (s:ss)) = continueWithFlags (Block ss) (doStep b) where 
  doStep (Block ((If e (Block ss1) (Block ss2)) : otherSs)) = do
    v <- evalE e
    if toBool v
      then return $ Block (ss1 ++ otherSs)
      else return $ Block (ss2 ++ otherSs)
  doStep (Block (w@(While e (Block ss)) : otherSs)) = do
    v <- evalE e
    if toBool v
      then return $ Block (ss ++ [w] ++ otherSs)
      else return $ Block otherSs
  doStep (Block (a@(Assign (v, _) e) : otherSs)) = do
    newState <- evalS a
    return $ Block otherSs
  doStep (Block ((Repeat b e) : otherSs)) = doStep (Block (While (Op1 Not e) b : otherSs))
  doStep (Block (empty : otherSs)) = return $ Block otherSs
  doStep b@(Block []) = return b

-- | Evaluate this block for a specified number of steps
boundedStep :: Int -> Block -> State EvalEnv Block
boundedStep 0 b = return b
boundedStep _ b | final b = return b
boundedStep n b = step b >>= boundedStep (n - 1)

-- | Evaluate this block for a specified number of steps, using the specified store
steps :: Int -> Block -> EvalEnv -> (Block, EvalEnv)
steps n block = S.runState (boundedStep n block)

-- | Is this block completely evaluated?
final :: Block -> Bool
final (Block []) = True
final _ = False

allStep :: Block -> State EvalEnv Block
allStep b | final b = return b
allStep b = step b >>= allStep

-- | Evaluate this block to completion
execStep :: Block -> EvalEnv -> EvalEnv
execStep b = S.execState (allStep b)

data Stepper = Stepper
  { filename :: Maybe String,
    block :: Block,
    env :: EvalEnv,
    history :: Maybe Stepper
  }

initialStepper :: Stepper
initialStepper =
  Stepper
    { filename = Nothing,
      block = mempty,
      env = C.emptyContext,
      history = Nothing
    }

stepForward :: Stepper -> Stepper
stepForward ss =
  let (curBlock, curEnv) = steps 1 (block ss) (env ss)
   in ss {block = curBlock, env = curEnv, history = Just ss}

stepForwardN :: Stepper -> Int -> Stepper
stepForwardN ss 0 = ss
stepForwardN ss n =
  let nextStepper = stepForward ss
   in stepForwardN nextStepper (n - 1)

stepBackward :: Stepper -> Maybe Stepper
stepBackward = history

stepBackwardN :: Stepper -> Int -> Maybe Stepper
stepBackwardN ss 0 = Just ss
stepBackwardN ss n =
  let prevStepper = stepBackward ss
   in case prevStepper of
        Just ss' -> stepBackwardN ss' (n - 1)
        _ -> Nothing

-- Fill in `undefined` below
stepper :: IO ()
stepper = go initialStepper
  where
    go :: Stepper -> IO ()
    go ss = do
      prompt ss
      putStr (fromMaybe "Lu" (filename ss) ++ "> ")
      hFlush stdout
      str <- getLine
      case List.uncons (words str) of
        -- load a file for stepping
        Just (":l", [fn]) -> do
          parseResult <- LuParser.parseLuFile fn
          case parseResult of
            (Left _) -> do
              putStr "Failed to parse file"
              go ss
            (Right b) -> do
              putStr ("Loaded " ++ fn ++ ", initializing stepper\n")
              go (ss {filename = Just fn, block = b})
        -- dump the store
        Just (":d", _) -> do
          putStrLn (pretty (env ss))
          go ss
        -- quit the stepper
        Just (":q", _) -> return ()
        -- run current block to completion
        Just (":r", _) ->
          let s' = execWithoutError (block ss) (env ss)
           in go ss {block = mempty, env = s', history = Just ss}
        -- next statement (could be multiple)
        Just (":n", strs) -> do
          let numSteps :: Int
              numSteps = case readMaybe (concat strs) of
                Just x -> x
                Nothing -> 1
          let newStepper = stepForwardN ss numSteps
          go newStepper
        -- previous statement
        -- NOTE: this should revert steps of the evaluator not
        -- commands to the stepper. With :n 5 followed by :p
        -- it should back up a single statement, not five statements.
        Just (":p", strs) -> do
          let numSteps :: Int
              numSteps = case readMaybe (concat strs) of
                Just x -> x
                Nothing -> 1

          let newStepper = stepBackwardN ss numSteps
          case newStepper of
            Just ss' -> go ss'
            _ -> do
              putStr "No History to revert..."
              go ss

        -- evaluate an expression in the current state
        _ -> case LuParser.parseLuExp str of
          Right exp -> do
            let v = evaluate exp (env ss)
            putStrLn (pretty v)
            go ss
          Left _s -> do
            putStrLn "?"
            go ss
    prompt :: Stepper -> IO ()
    prompt Stepper {block = Block []} = return ()
    prompt Stepper {block = Block (s : _)} =
      putStr "--> " >> putStrLn (pretty s)
