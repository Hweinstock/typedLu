module LuEvaluator where

import Control.Monad (when)
import Data.List qualified as List
import Data.Map (Map, (!?))
import Data.Map qualified as Map
import LuParser qualified
import LuSyntax
import LuTypes
import Context (Context)
import Context qualified as C
import State (State)
import State qualified as S
import Test.HUnit (Counts, Test (..), runTestTT, (~:), (~?=))
import Test.QuickCheck qualified as QC

data EvalEnv = EvalEnv { 
  context :: Context Value,
  tables :: Map Name Table
} deriving Show

toStore :: EvalEnv -> Store
toStore env = Map.insert globalTableName gTable (tables env) where 
  gTable = Map.mapKeys StringVal (C.gMap (context env))

fromStore :: Store -> EvalEnv 
fromStore s = case Map.lookup globalTableName s of 
  Nothing -> emptyEvalEnv -- Shouldn't hit this cae.  
  Just globalTable -> newEnv where 
    newEnv = let initEnv = emptyEvalEnv in 
      initEnv {context = C.setGMap (context initEnv) newGlobalTable, tables = newTables} 
        where 
          newTables = Map.filterWithKey (\k _ -> k /= globalTableName) s
          newGlobalTable = Map.filterWithKey (\k _ -> k /= "@") (Map.mapKeys keyFunc globalTable)
          where 
            keyFunc (StringVal s) = s 
            keyFunc _ = "@"


instance PP EvalEnv where 
  pp env = undefined 

instance QC.Arbitrary EvalEnv where 
  arbitrary = undefined 
  shrink = undefined

emptyEvalEnv :: EvalEnv 
emptyEvalEnv = EvalEnv {context = C.emptyContext, tables = Map.empty}


type Store = Map Name Table

type Table = Map Value Value

globalTableName :: Name
globalTableName = "_G"

returnValueName :: Name 
returnValueName = "@R"

returnFlagName :: Name 
returnFlagName = "@F"

haltFlagName :: Name 
haltFlagName = "_H"

errorCodeName :: Name 
errorCodeName = "_E"

returnValueRef :: Reference
returnValueRef = (globalTableName, StringVal returnValueName)

returnFlagRef :: Reference
returnFlagRef = (globalTableName, StringVal returnFlagName)

haltFlagRef :: Reference 
haltFlagRef = (globalTableName, StringVal haltFlagName)

errorCodeRef :: Reference 
errorCodeRef = (globalTableName, StringVal errorCodeName)

throwError :: ErrorCode -> State EvalEnv () 
throwError ec = update errorCodeRef (ErrorVal ec) >> update haltFlagRef (BoolVal True) 

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

initialEnv :: EvalEnv
initialEnv = fromStore $ Map.singleton globalTableName Map.empty

extendedEnv :: EvalEnv
extendedEnv = fromStore m where 
  m = Map.fromList
    [ ( globalTableName,
        Map.fromList
          [ (StringVal "x", IntVal 3),
            (StringVal "t", TableVal "_t1")
          ]
      ),
      ( "_t1",
        Map.fromList
          [ (StringVal "y", BoolVal True),
            (IntVal 2, TableVal "_t1")
          ]
      )
    ]

type Reference = (Name, Value)

xref :: Reference
xref = ("_G", StringVal "x")

yref :: Reference
yref = ("_t1", StringVal "y")

tableFromState :: Name -> State EvalEnv (Maybe Table)
tableFromState tname = Map.lookup tname . toStore <$> S.get

index :: Reference -> State EvalEnv Value
index (tableName, key) = do
  t <- tableFromState tableName
  case t of
    Just t -> case Map.lookup key t of
      Just v -> return v
      _ -> return NilVal
    _ -> return NilVal

update :: Reference -> Value -> State EvalEnv ()
update (tableName, NilVal) newVal = S.get >>= \s -> return ()
update (tableName, key) newVal = do
  t <- tableFromState tableName
  -- not right
  S.modify (updateEnv t)
  where
    updateEnv :: Maybe Table -> EvalEnv -> EvalEnv 
    updateEnv maybeTable env = 
      case maybeTable of 
        Nothing -> env
        Just t -> fromStore (Map.insert tableName (Map.insert key newVal t) (toStore env))

allocateTable :: [(Value, Value)] -> State EvalEnv Value
allocateTable assocs = do
  env <- S.get
  let store = toStore env 
  -- make a fresh name for the new table
  let n = length (Map.keys store)
  let tableName = "_t" ++ show n
  -- make sure we don't have a nil key or value
  let assocs' = filter nonNil assocs
  -- update the store
  S.put (fromStore (Map.insert tableName (Map.fromList assocs') store))
  return (TableVal tableName)

-- Keep nil out of the table
nonNil :: (Value, Value) -> Bool
nonNil (k, v) = k /= NilVal && v /= NilVal

-- | Convert a variable into a reference into the store.
-- Fails when the var is `t.x` or t[1] and `t` is not defined in the store
-- when the var is `2.y` or `nil[2]` (i.e. not a `TableVal`)
-- or when the var is t[nil]
resolveVar :: Var -> State EvalEnv (Maybe Reference)
resolveVar (Name n) = do
  mGlobalTable <- tableFromState globalTableName
  return $ case mGlobalTable of
    Just globalTable -> Just (globalTableName, StringVal n)
    _ -> Nothing
resolveVar (Dot exp n) = do
  mGlobalTable <- tableFromState globalTableName
  e <- evalE exp
  return $ case (e, mGlobalTable) of
    (TableVal tname, Just globalTable) -> Just (tname, StringVal n)
    _ -> Nothing
resolveVar (Proj exp1 exp2) = do
  e1 <- evalE exp1
  e2 <- evalE exp2
  return $ case (e1, e2) of
    (_, NilVal) -> Nothing
    (TableVal t1, v) -> Just (t1, v)
    _ -> Nothing

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
        Just r -> index r
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
          let parameterNames = map fst ps
          let pOrigValuesVars = map (Var . Name) parameterNames
          pOrigValues <- seqEval pOrigValuesVars

          -- Initialize parameters as values. 
          setVars parameterNames pps 
          eval b
          returnValue <- evalE (Var (Name returnValueName))
          -- Reset Flags/ReturnValue
          update returnValueRef NilVal 
          update returnFlagRef (BoolVal False)

          -- Unscope Parameters i.e. NilValue them. 
          setVars parameterNames (map Val pOrigValues)
          return returnValue
        _ -> return NilVal

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
seqEval = foldr seqEvalHelper (return []) where 
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

getTableSizeState :: String -> State EvalEnv (Maybe Int)
getTableSizeState v =
  S.get >>= \s -> return $ do
    targetTable <- Map.lookup v (toStore s)
    return $ length targetTable

evalOp1 :: Uop -> Value -> State EvalEnv Value
evalOp1 Neg (IntVal v) = return $ IntVal $ negate v
evalOp1 Len (StringVal v) = return $ IntVal $ length v
evalOp1 Len (TableVal v) = do
  ml <- getTableSizeState v
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
evalS s = continueWithFlags () (doEvalS s) where 
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
      Just ref -> update ref e'
      _ -> return ()
  doEvalS s@(Repeat b e) = evalS (While (Op1 Not e) b) -- keep evaluating block b until expression e is true
  doEvalS (Return e) = evalS (Assign (Name returnValueName, UnknownType) e) >> evalS (Assign (Name returnFlagName, BooleanType) (Val (BoolVal True)))
  doEvalS Empty = return () -- do nothing

exec :: Block -> EvalEnv -> EvalEnv
exec = S.execState . eval
