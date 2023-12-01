module LuEvaluator where

import Control.Monad (when)
import Data.List qualified as List
import Data.Map (Map, (!?))
import Data.Map qualified as Map
import LuParser qualified
import LuSyntax
import State (State)
import State qualified as S
import Test.HUnit (Counts, Test (..), runTestTT, (~:), (~?=))
import Test.QuickCheck qualified as QC

type Store = Map Name Table

type Table = Map Value Value

globalTableName :: Name
globalTableName = "_G"

returnValueName :: Name 
returnValueName = "_R"

returnValueRef :: Reference
returnValueRef = (globalTableName, StringVal returnValueName)

returnFlagName :: Name 
returnFlagName = "_F"

returnFlagRef :: Reference
returnFlagRef = (globalTableName, StringVal returnFlagName)

isReturnFlagSet :: State Store Bool 
isReturnFlagSet = do 
  currentState <- S.get
  value <- evalE (Var (Name returnFlagName))
  return $ case value of 
    (BoolVal True) -> True 
    _ -> False

initialStore :: Store
initialStore = Map.singleton globalTableName Map.empty

extendedStore :: Store
extendedStore =
  Map.fromList
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

tableFromState :: Name -> State Store (Maybe Table)
tableFromState tname = Map.lookup tname <$> S.get

index :: Reference -> State Store Value
index (tableName, key) = do
  t <- tableFromState tableName
  case t of
    Just t -> case Map.lookup key t of
      Just v -> return v
      _ -> return NilVal
    _ -> return NilVal

update :: Reference -> Value -> State Store ()
update (tableName, NilVal) newVal = S.get >>= \s -> return ()
update (tableName, key) newVal = do
  t <- tableFromState tableName
  S.modify (updateStore t)
  where
    updateStore :: Maybe Table -> (Store -> Store)
    updateStore maybeTable =
      case maybeTable of
        Just t -> Map.insert tableName (Map.insert key newVal t)
        _ -> id

allocateTable :: [(Value, Value)] -> State Store Value
allocateTable assocs = do
  store <- S.get
  -- make a fresh name for the new table
  let n = length (Map.keys store)
  let tableName = "_t" ++ show n
  -- make sure we don't have a nil key or value
  let assocs' = filter nonNil assocs
  -- update the store
  S.put (Map.insert tableName (Map.fromList assocs') store)
  return (TableVal tableName)

-- Keep nil out of the table
nonNil :: (Value, Value) -> Bool
nonNil (k, v) = k /= NilVal && v /= NilVal

-- | Convert a variable into a reference into the store.
-- Fails when the var is `t.x` or t[1] and `t` is not defined in the store
-- when the var is `2.y` or `nil[2]` (i.e. not a `TableVal`)
-- or when the var is t[nil]
resolveVar :: Var -> State Store (Maybe Reference)
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
evalE :: Expression -> State Store Value
evalE (Var v) = do
  mr <- resolveVar v -- see above
  case mr of
    Just r -> index r
    Nothing -> return NilVal
evalE (Val v) = return v
evalE (Op2 e1 o e2) = evalOp2 o <$> evalE e1 <*> evalE e2
evalE (Op1 o e) = do
  s <- S.get
  e' <- evalE e
  evalOp1 o e'
evalE (TableConst _fs) = evalTableConst _fs
evalE (Call func pps) = do 
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
setVars :: [Name] -> [Expression] -> State Store () 
setVars pNames pps = do 
  values <- seqEval pps
  foldr seqSet (return ()) (zip values pNames)
  where 
    seqSet :: (Value, Name) -> State Store () -> State Store () 
    seqSet p@(v, n) s = s >> evalS (Assign (Name n) (Val v))
    

-- | Evaluate a list of expressions in sequence (passing state along right to left), returning all values in final state monad. 
seqEval :: [Expression] -> State Store [Value]
seqEval = foldr seqEvalHelper (return []) where 
  seqEvalHelper :: Expression -> State Store [Value] -> State Store [Value]
  seqEvalHelper e s = do 
    curValues <- s
    newValue <- evalE e 
    return (newValue : curValues)

fieldToPair :: TableField -> State Store (Value, Value)
fieldToPair (FieldName n exp) = do
  e <- evalE exp
  return (StringVal n, e)
fieldToPair (FieldKey exp1 exp2) = do
  e1 <- evalE exp1
  e2 <- evalE exp2
  return (e1, e2)

accuFieldToPair :: TableField -> State Store [(Value, Value)] -> State Store [(Value, Value)]
accuFieldToPair tf accu = do
  pair <- fieldToPair tf
  rest <- accu
  return (pair : rest)

evalTableConst :: [TableField] -> State Store Value
evalTableConst xs = do
  vs <- helper xs
  allocateTable vs
  where
    helper :: [TableField] -> State Store [(Value, Value)]
    helper = foldr accuFieldToPair (return [])

getTableSizeState :: String -> State Store (Maybe Int)
getTableSizeState v =
  S.get >>= \s -> return $ do
    targetTable <- Map.lookup v s
    return $ length targetTable

evalOp1 :: Uop -> Value -> State Store Value
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
evalOp1 _ _ = return NilVal

evalOp2 :: Bop -> Value -> Value -> Value
evalOp2 Plus (IntVal i1) (IntVal i2) = IntVal (i1 + i2)
evalOp2 Minus (IntVal i1) (IntVal i2) = IntVal (i1 - i2)
evalOp2 Times (IntVal i1) (IntVal i2) = IntVal (i1 * i2)
evalOp2 Divide (IntVal _) (IntVal 0) = NilVal
evalOp2 Divide (IntVal i1) (IntVal i2) = IntVal (i1 `div` i2)
evalOp2 Modulo (IntVal i1) (IntVal 0) = NilVal
evalOp2 Modulo (IntVal i1) (IntVal i2) = IntVal $ i1 `mod` i2
evalOp2 Eq v1 v2 = BoolVal $ v1 == v2
evalOp2 Gt v1 v2 = BoolVal $ v1 > v2
evalOp2 Ge v1 v2 = BoolVal $ v1 >= v2
evalOp2 Lt v1 v2 = BoolVal $ v1 < v2
evalOp2 Le v1 v2 = BoolVal $ v1 <= v2
evalOp2 Concat (StringVal s1) (StringVal s2) = StringVal (s1 ++ s2)
evalOp2 _ _ _ = NilVal

evaluate :: Expression -> Store -> Value
evaluate e = S.evalState (evalE e)

-- | Determine whether a value should be interpreted as true or false when
-- used as a condition.
toBool :: Value -> Bool
toBool (BoolVal False) = False
toBool NilVal = False
toBool _ = True

eval :: Block -> State Store ()
eval (Block ss) = mapM_ evalS ss

-- | Statement evaluator
evalS :: Statement -> State Store ()
evalS s = do 
  didReturn <- isReturnFlagSet 
  if didReturn then return () else doEvalS s where 
    doEvalS (If e s1 s2) = do
      v <- evalE e
      if toBool v then eval s1 else eval s2
    doEvalS w@(While e ss) = do
      v <- evalE e
      when (toBool v) $ do
        eval ss
        evalS w
    doEvalS (Assign v e) = do
      -- update global variable or table field v to value of e
      s <- S.get
      mRef <- resolveVar v
      e' <- evalE e
      case mRef of
        Just ref -> update ref e'
        _ -> return ()
    doEvalS s@(Repeat b e) = evalS (While (Op1 Not e) b) -- keep evaluating block b until expression e is true
    doEvalS (Return e) = evalS (Assign (Name returnValueName) e) >> evalS (Assign (Name returnFlagName) (Val (BoolVal True)))
    doEvalS Empty = return () -- do nothing

exec :: Block -> Store -> Store
exec = S.execState . eval
