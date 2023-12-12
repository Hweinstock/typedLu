module LuEvaluator where

import Context (Context, Environment, ExtendedContext, Reference (GlobalRef, LocalRef, TableRef))
import Context qualified as C
import Control.Monad (when)
import Data.List qualified as List
import Data.Map (Map, (!?))
import Data.Map qualified as Map
import LuParser qualified
import LuSyntax
import LuTypes
import State (State)
import State qualified as S
import Test.HUnit (Counts, Test (..), runTestTT, (~:), (~?=))
import Test.QuickCheck qualified as QC

type Store = Map Name Table

type Table = Map Value Value

data EvalEnv = EvalEnv
  { context :: Context Value,
    tableMap :: Map Name Table
  }
  deriving (Show)

instance ExtendedContext EvalEnv where
  emptyContext :: EvalEnv
  emptyContext = EvalEnv {context = C.emptyContext, tableMap = Map.empty}

  exitScope :: EvalEnv -> EvalEnv
  exitScope env = env {context = C.exitScope (context env)}

  enterScope :: EvalEnv -> EvalEnv
  enterScope env = env {context = C.enterScope (context env)}

instance Environment EvalEnv Value where
  getContext :: EvalEnv -> Context Value
  getContext = context

  setContext :: EvalEnv -> Context Value -> EvalEnv
  setContext env c = env {context = c}

  index :: Reference -> State EvalEnv Value
  index r = C.indexWithDefault r NilVal

  lookup :: Name -> State EvalEnv Value
  lookup = C.lookupWithUnknown NilVal

  indexTable :: (Name, Value) -> Value -> State EvalEnv Value
  indexTable (tname, tkey) d = do
    env <- S.get
    return $ case Map.lookup tname (tableMap env) of
      Just table -> case Map.lookup tkey table of
        Just v -> v
        _ -> d
      _ -> d

  updateTable :: (Name, Value) -> Value -> State EvalEnv ()
  updateTable (tname, tkey) v = do
    mTable <- tableFromState tname
    S.modify (updateTableHelper mTable)
    where
      updateTableHelper :: Maybe Table -> EvalEnv -> EvalEnv
      updateTableHelper mt env = case mt of
        Nothing -> env
        Just t -> env {tableMap = Map.insert tname (Map.insert tkey v t) (tableMap env)}

resolveVar :: Var -> State EvalEnv (Maybe Reference)
resolveVar (Name n) = do
  env <- S.get
  let localLookup = C.getLocal n env :: Maybe Value
  let globalLookup = C.getGlobal n env :: Maybe Value
  return $ case (localLookup, globalLookup) of
    (Just v, _) -> Just $ LocalRef n
    _ -> Just $ GlobalRef n
resolveVar (Dot exp n) = do
  e <- evalE exp
  return $ case e of
    TableVal tname -> Just (TableRef tname (StringVal n))
    _ -> Nothing
resolveVar (Proj exp1 exp2) = do
  e1 <- evalE exp1
  e2 <- evalE exp2
  return $ case (e1, e2) of
    (_, NilVal) -> Nothing
    (TableVal t1, v) -> Just (TableRef t1 v)
    _ -> Nothing

-- | Helper function to convert evaluation environment to Store (for testing and debugging)
toStore :: EvalEnv -> Store
toStore env = Map.insert globalTableName (C.gMap (context env)) (tableMap env)

-- | Helper function to convert Store to evaluation environment (for testing and debugging)
fromStore :: Store -> EvalEnv
fromStore s = case Map.lookup globalTableName s of
  Nothing -> C.emptyContext -- Shouldn't hit this cae.
  Just globalTable -> newEnv
    where
      newEnv =
        let initEnv = C.emptyContext
         in (C.setGMap globalTable initEnv) {tableMap = newTables}
        where
          newTables = Map.filterWithKey (\k _ -> k /= globalTableName) s

instance PP EvalEnv where
  pp env = undefined

globalTableName :: Name
globalTableName = "_G"

returnValueName :: Name
returnValueName = "@R"

returnFlagName :: Name
returnFlagName = "@F"

haltFlagName :: Name
haltFlagName = "@H"

errorCodeName :: Name
errorCodeName = "@E"

returnValueRef :: Reference
returnValueRef = GlobalRef returnValueName

returnFlagRef :: Reference
returnFlagRef = GlobalRef returnFlagName

haltFlagRef :: Reference
haltFlagRef = GlobalRef haltFlagName

errorCodeRef :: Reference
errorCodeRef = GlobalRef errorCodeName

throwError :: ErrorCode -> State EvalEnv ()
throwError ec = C.update errorCodeRef (ErrorVal ec) >> C.update haltFlagRef (BoolVal True)

didReturnOrHalt :: State EvalEnv Bool
didReturnOrHalt = do
  didReturn <- isReturnFlagSet
  didHalt <- isHaltFlagSet
  return $ didReturn || didHalt

-- | Check if we should terminate, if so return stopCase otherwise continue with eval
continueWithFlags :: a -> State EvalEnv a -> State EvalEnv a
continueWithFlags stopCase continue = do
  shouldStop <- didReturnOrHalt
  if shouldStop then return stopCase else continue

isError :: Value -> Bool
isError (ErrorVal _) = True
isError _ = False

didError :: EvalEnv -> Bool
didError env =
  case S.evalState (C.index haltFlagRef) env of
    (BoolVal True) -> True
    _ -> False

getError :: EvalEnv -> ErrorCode
getError env =
  case S.evalState (C.index errorCodeRef) env of
    (ErrorVal e) -> e
    _ -> UnknownError

isFlagSet :: Name -> State EvalEnv Bool
isFlagSet n = do
  value <- evalE (Var (Name n))
  return $ case value of
    (BoolVal True) -> True
    _ -> False

isReturnFlagSet :: State EvalEnv Bool
isReturnFlagSet = isFlagSet returnFlagName

isHaltFlagSet :: State EvalEnv Bool
isHaltFlagSet = isFlagSet haltFlagName

tableFromState :: Name -> State EvalEnv (Maybe Table)
tableFromState tname | tname == globalTableName = Just . C.gMap . context <$> S.get
tableFromState tname = Map.lookup tname . tableMap <$> S.get

allocateTable :: [(Value, Value)] -> State EvalEnv Value
allocateTable assocs = do
  -- make a fresh name for the new table
  n <- length . Map.keys . tableMap <$> S.get
  let tableName = "_t" ++ show n
  -- make sure we don't have a nil key or value
  let assocs' = Map.fromList (filter nonNil assocs)
  -- update the store
  S.modify (\env -> env {tableMap = Map.insert tableName assocs' (tableMap env)})
  return (TableVal tableName)

-- Keep nil out of the table
nonNil :: (Value, Value) -> Bool
nonNil (k, v) = k /= NilVal && v /= NilVal

-- | Expression evaluator
evalE :: Expression -> State EvalEnv Value
evalE e = do
  v <- doEvalE e
  case v of
    (ErrorVal ec) -> throwError ec >> return v
    _ -> return v
  where
    doEvalE (Var v) = do
      mr <- resolveVar v -- see above
      case mr of
        Just r -> C.index r
        Nothing -> return NilVal
    doEvalE (Val v) = return v
    doEvalE (Op2 e1 o e2) = do evalOp2 o <$> evalE e1 <*> evalE e2
    doEvalE (Op1 o e) = do
      s <- S.get
      e' <- evalE e
      evalOp1 o e'
    doEvalE (TableConst _fs) = evalTableConst _fs
    doEvalE (Call func pps) = do
      fv <- evalE (Var func)
      case fv of
        (FunctionVal ps rt b) -> do
          parameters <- evalParameters (map fst ps) pps
          let extParameters = (returnValueName, NilVal) : (returnFlagName, BoolVal False) : parameters
          C.prepareFunctionEnv extParameters
          eval b
          returnValue <- evalE (Var (Name returnValueName))
          S.modify C.exitScope
          return returnValue
        _ -> return NilVal

evalParameters :: [Name] -> [Expression] -> State EvalEnv [(Name, Value)]
evalParameters pNames pExps = do
  pValues <- seqEval pExps
  return $ zip pNames pValues

-- | Set list of parameters to list of expressions, return resulting state.
setVars :: [Name] -> [Expression] -> State EvalEnv ()
setVars pNames pps = do
  values <- seqEval pps
  foldr seqSet (return ()) (zip values pNames)
  where
    seqSet :: (Value, Name) -> State EvalEnv () -> State EvalEnv ()
    seqSet p@(v, n) s = s >> evalS (Assign (Name n, UnknownType) (Val v))

-- | Evaluate a list of expressions in sequence (passing state along right to left), returning all values in final state monad.
seqEval :: [Expression] -> State EvalEnv [Value]
seqEval = foldr seqEvalHelper (return [])
  where
    seqEvalHelper :: Expression -> State EvalEnv [Value] -> State EvalEnv [Value]
    seqEvalHelper e s = do
      curValues <- s
      newValue <- evalE e
      return (newValue : curValues)

fieldToPair :: TableField -> State EvalEnv (Value, Value)
fieldToPair (FieldName n exp) = do
  e <- evalE exp
  return (StringVal n, e)
fieldToPair (FieldKey exp1 exp2) = do
  e1 <- evalE exp1
  e2 <- evalE exp2
  return (e1, e2)

accuFieldToPair :: TableField -> State EvalEnv [(Value, Value)] -> State EvalEnv [(Value, Value)]
accuFieldToPair tf accu = do
  pair <- fieldToPair tf
  rest <- accu
  return (pair : rest)

evalTableConst :: [TableField] -> State EvalEnv Value
evalTableConst xs = do
  vs <- helper xs
  allocateTable vs
  where
    helper :: [TableField] -> State EvalEnv [(Value, Value)]
    helper = foldr accuFieldToPair (return [])

getTableSize :: String -> State EvalEnv (Maybe Int)
getTableSize v = do
  s <- S.get
  return $ case Map.lookup v (tableMap s) of
    Just t -> Just $ length t
    _ -> Nothing

evalOp1 :: Uop -> Value -> State EvalEnv Value
evalOp1 Neg (IntVal v) = return $ IntVal $ negate v
evalOp1 Len (StringVal v) = return $ IntVal $ length v
evalOp1 Len (TableVal v) = do
  ml <- getTableSize v
  return $ case ml of
    Just l -> IntVal l
    _ -> NilVal
evalOp1 Len iv@(IntVal v) = return iv
evalOp1 Len (BoolVal True) = return $ IntVal 1
evalOp1 Len (BoolVal False) = return $ IntVal 0
evalOp1 Not v = return $ BoolVal $ not $ toBool v
evalOp1 _ _ = return $ ErrorVal IllegalArguments

evalOp2 :: Bop -> Value -> Value -> Value
evalOp2 Plus (IntVal i1) (IntVal i2) = IntVal (i1 + i2)
evalOp2 Minus (IntVal i1) (IntVal i2) = IntVal (i1 - i2)
evalOp2 Times (IntVal i1) (IntVal i2) = IntVal (i1 * i2)
evalOp2 Divide (IntVal _) (IntVal 0) = ErrorVal DivideByZero
evalOp2 Divide (IntVal i1) (IntVal i2) = IntVal (i1 `div` i2)
evalOp2 Modulo (IntVal i1) (IntVal 0) = ErrorVal DivideByZero
evalOp2 Modulo (IntVal i1) (IntVal i2) = IntVal $ i1 `mod` i2
evalOp2 Eq v1 v2 = BoolVal $ v1 == v2
evalOp2 Gt v1 v2 = BoolVal $ v1 > v2
evalOp2 Ge v1 v2 = BoolVal $ v1 >= v2
evalOp2 Lt v1 v2 = BoolVal $ v1 < v2
evalOp2 Le v1 v2 = BoolVal $ v1 <= v2
evalOp2 Concat (StringVal s1) (StringVal s2) = StringVal (s1 ++ s2)
evalOp2 _ _ _ = ErrorVal IllegalArguments

evaluate :: Expression -> EvalEnv -> Value
evaluate e = S.evalState (evalE e)

-- | Determine whether a value should be interpreted as true or false when
-- used as a condition.
toBool :: Value -> Bool
toBool (BoolVal False) = False
toBool NilVal = False
toBool _ = True

eval :: Block -> State EvalEnv ()
eval (Block ss) = mapM_ evalS ss

-- | Statement evaluator
evalS :: Statement -> State EvalEnv ()
evalS s = continueWithFlags () (doEvalS s)
  where
    doEvalS (If e s1 s2) = do
      v <- evalE e
      if toBool v then eval s1 else eval s2
    doEvalS w@(While e ss) = do
      v <- evalE e
      when (toBool v) $ do
        eval ss
        evalS w
    doEvalS (Assign (v, _) e) = do
      -- update global variable or table field v to value of e
      mRef <- resolveVar v
      e' <- evalE e
      case mRef of
        Just ref -> C.update ref e'
        _ -> return ()
    doEvalS s@(Repeat b e) = evalS (While (Op1 Not e) b) -- keep evaluating block b until expression e is true
    doEvalS (Return e) = evalS (Assign (Name returnValueName, UnknownType) e) >> evalS (Assign (Name returnFlagName, BooleanType) (Val (BoolVal True)))
    doEvalS Empty = return () -- do nothing

execWithoutError :: Block -> EvalEnv -> EvalEnv
execWithoutError = S.execState . eval

exec :: Block -> EvalEnv -> Either String EvalEnv
exec b env =
  let finalEnv = S.execState (eval b) env
   in if didError finalEnv
        then Left $ (show . getError) finalEnv
        else return finalEnv
