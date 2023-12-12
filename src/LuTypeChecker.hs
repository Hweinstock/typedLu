module LuTypeChecker where

import Context (Context, Environment, ExtendedContext, Reference (GlobalRef, LocalRef, TableRef))
import Context qualified as C
import Control.Monad
import Control.Monad.Except (ExceptT, MonadError (throwError), runExcept, runExceptT)
import Control.Monad.State (MonadState (get, put), StateT (runStateT))
import Control.Monad.State qualified as State
import Data.List (nub)
import Data.Map (Map)
import Data.Map qualified as Map
import LuSyntax
import LuTypes
import Stack qualified
import State (State)
import State qualified as S

data TypeEnv = TypeEnv
  { uncalledFuncs :: Map Reference Value,
    context :: Context LType
  }
  deriving (Show)

instance ExtendedContext TypeEnv where
  emptyContext :: TypeEnv
  emptyContext = TypeEnv {context = C.emptyContext, uncalledFuncs = Map.empty}

  enterScope :: TypeEnv -> TypeEnv
  enterScope env = env {context = C.enterScope (context env)}

  exitScope :: TypeEnv -> TypeEnv
  exitScope env = env {context = C.exitScope (context env)}

instance Environment TypeEnv LType where
  getContext :: TypeEnv -> Context LType
  getContext = context

  setContext :: TypeEnv -> Context LType -> TypeEnv
  setContext env newContext = env {context = newContext}

  index :: (MonadState TypeEnv m) => Reference -> m LType
  index r@(GlobalRef _) = C.indexWithDefault r NilType
  index r@(LocalRef _) = C.indexWithDefault r UnknownType
  index r = C.indexWithDefault r NilType

  indexTable :: (MonadState TypeEnv m) => (Name, Value) -> LType -> m LType
  indexTable _ = return

  updateTable :: (MonadState TypeEnv m) => (Name, Value) -> LType -> m ()
  updateTable _ _ = return ()

  resolveName :: (MonadState TypeEnv m) => Name -> m (Reference, LType)
  resolveName = C.resolveNameWithUnknown UnknownType

emptyTypeEnv :: TypeEnv
emptyTypeEnv = TypeEnv {context = C.emptyContext, uncalledFuncs = Map.empty}

addUncalledFunc :: Reference -> Value -> TypeEnv -> TypeEnv
addUncalledFunc ref v env = env {uncalledFuncs = Map.insert ref v (uncalledFuncs env)}

getUncalledFunc :: TypeEnv -> Reference -> Maybe Value
getUncalledFunc env n = Map.lookup n (uncalledFuncs env)

removeUncalledFunc :: TypeEnv -> Reference -> TypeEnv
removeUncalledFunc env n = env {uncalledFuncs = Map.delete n (uncalledFuncs env)}

-- | Update variable type in store. Handles case where we need to add function to uncalled map.
updateRef :: (MonadError String m, MonadState TypeEnv m) => Reference -> LType -> Expression -> m ()
updateRef ref t exp = do
  C.update ref t
  case (t, exp) of
    (FunctionType _ _, Val f@(FunctionVal pms rt b)) -> preCheckFuncBody ref pms rt b
    _ -> return ()

-- type TypecheckerState a = State TypeEnv (Either String a)
-- type TypecheckerState m a = (MonadError String m, MonadState Int m) => m a

class Synthable a where
  synth :: (MonadError String m, MonadState TypeEnv m) => a -> m LType

instance Synthable Uop where
  synth Neg = return $ FunctionType IntType IntType
  synth Not = return $ FunctionType AnyType BooleanType
  synth Len = return $ FunctionType (UnionType IntType (UnionType StringType (TableType AnyType AnyType))) IntType

instance Synthable Bop where
  synth Plus = return $ FunctionType IntType (FunctionType IntType IntType)
  synth Minus = return $ FunctionType IntType (FunctionType IntType IntType)
  synth Times = return $ FunctionType IntType (FunctionType IntType IntType)
  synth Divide = return $ FunctionType IntType (FunctionType IntType IntType)
  synth Modulo = return $ FunctionType IntType (FunctionType IntType IntType)
  synth Eq = return $ FunctionType AnyType (FunctionType AnyType BooleanType)
  synth Gt = return $ FunctionType AnyType (FunctionType AnyType BooleanType)
  synth Ge = return $ FunctionType AnyType (FunctionType AnyType BooleanType)
  synth Lt = return $ FunctionType AnyType (FunctionType AnyType BooleanType)
  synth Le = return $ FunctionType AnyType (FunctionType AnyType BooleanType)
  synth Concat = return $ FunctionType StringType (FunctionType StringType StringType)

instance Synthable Value where
  synth NilVal = return NilType
  synth (IntVal _) = return IntType
  synth (BoolVal _) = return BooleanType
  synth (StringVal _) = return StringType
  synth (TableVal n) = undefined -- what is this case?
  synth (ErrorVal _) = return NilType -- shouldn't hit this case.
  synth (FunctionVal pms rt b) = do
    return $ synthFunc pms rt
    where
      synthFunc :: [Parameter] -> LType -> LType
      synthFunc [] rt = FunctionType Never rt
      synthFunc [(_, t)] rt = FunctionType t rt
      synthFunc ((_, t) : ps) rt = FunctionType t (synthFunc ps rt)

instance Synthable Var where
  synth :: (MonadError String m, MonadState TypeEnv m) => Var -> m LType
  synth (Name n) = snd <$> C.resolveName n
  synth (Dot exp n) = do
    expType <- synthesis exp
    case expType of
      t@(TableType t1 t2) -> typecheckTableAccess t StringType Never >> return t2
      _ -> throwError "Cannot access non table type via dot method"
  -- return $ case eExpType of
  --   Left l -> Left l
  --   Right tExp@(TableType t1 t2) -> case typecheckTableAccess tExp StringType Never of
  --     Right () -> Right t2
  --     Left l -> Left l
  --   Right _ -> Left "Cannot access non table type via dot method."
  synth (Proj tExp kExp) = do
    tableType <- synthesis tExp
    keyType <- synthesis kExp
    typecheckTableAccess tableType keyType Never
    case tableType of
      TableType t1 t2 -> return t2
      _ -> throwError "Cannot access not table type via proj method."

-- return $ case (eTableType, eKeyType) of
--   (Left l, _) -> Left l
--   (_, Left l) -> Left l
--   (Right tableType@(TableType t1 t2), Right keyType) -> case typecheckTableAccess tableType keyType Never of
--     Right () -> Right t2
--     Left l -> Left l
--   _ -> Left "Cannot access not table type via proj method."

instance Synthable [TableField] where
  synth tfs = do
    typePairs <- foldr synthTableField (return []) tfs
    let (keyTypes, valTypes) = unzip typePairs
    return $ TableType (constructUnionType keyTypes) (constructUnionType valTypes)
    where
      -- return $ case eTypePairs of
      --   Left l -> Left l
      --   Right typePairs -> do
      --     let (keyTypes, valTypes) = unzip typePairs
      --     Right $ TableType (constructUnionType keyTypes) (constructUnionType valTypes)

      synthTableField :: (MonadError String m, MonadState TypeEnv m) => TableField -> m [(LType, LType)] -> m [(LType, LType)]
      synthTableField (FieldName n e) res = synthTableField (FieldKey (Val (StringVal n)) e) res
      synthTableField (FieldKey e1 e2) res = do
        pairsSoFar <- res
        t1 <- synthesis e1
        t2 <- synthesis e2
        return $ (t1, t2) : pairsSoFar

-- case (ePairs, eT1, eT2) of
--   (Right pairs, Right t1, Right t2) -> return $ Right ((t1, t2) : pairs)
--   (Left l, _, _) -> return $ Left l
--   (_, Left l, _) -> return $ Left l
--   (_, _, Left l) -> return $ Left l

instance Synthable (Statement, LType) where
  -- \| Given a statement, an environment and an expected return type, check if the types are consistent in the statement.
  synth :: (MonadError String m, MonadState TypeEnv m) => (Statement, LType) -> m LType
  synth (Assign (v, UnknownType) exp, expectedReturnType) = do
    expType <- synthesis exp
    typeCheckAssign v expType exp
  synth (Assign (v, t) exp, expectedReturnType) = typeCheckAssign v t exp
  synth (If exp b1 b2, expectedReturnType) = typeCheckConditionalBlocks exp expectedReturnType [b1, b2] "Non-boolean in if condition"
  synth (While exp b, expectedReturnType) = typeCheckConditionalBlocks exp expectedReturnType [b] "Non-boolean in while condition"
  synth (Empty, expectedReturnType) = return NilType
  synth (Repeat b exp, expectedReturnType) = typeCheckConditionalBlocks exp expectedReturnType [b] "Non-boolean in repeat condition"
  synth (Return exp, expectedReturnType) = do
    sameType <- checker exp expectedReturnType
    if sameType
      then return expectedReturnType
      else throwError "return type mismatch"

-- case eRes of
--   Left error -> return $ Left error
--   Right False -> throwError "Return" expectedReturnType exp
--   Right True -> return $ Right expectedReturnType

instance Synthable (Block, LType) where
  -- \| Given a block, an environment, and an expected return type, return the type returned by the block.
  synth :: (MonadError String m, MonadState TypeEnv m) => (Block, LType) -> m LType
  synth (Block [s], expectedReturnType) = synth (s, expectedReturnType)
  synth (Block (s : ss), expectedReturnType) = do
    statementType <- synth (s, expectedReturnType)
    case s of
      (Return exp) -> do
        sameType <- checker exp statementType
        if sameType
          then return expectedReturnType
          else throwError "BlockType mismatch"
      _ -> synth (Block ss, expectedReturnType)

  -- case (s, curCheck) of
  --   (_, Left l) -> return $ Left l
  --   (Return exp, Right t) -> do
  --     eRes <- checker exp t
  --     case eRes of
  --       Left l -> return $ Left l
  --       Right False -> throwError "BlockType" expectedReturnType exp
  --       Right True -> return $ Right t
  --   (_, Right t) -> synth (Block ss, expectedReturnType)
  synth (Block [], expectedReturnType) = return NilType

-- Given AST and env, typechecks it.
-- typeCheckAST :: (MonadError String m) => Block -> TypeEnv -> m ()
-- typeCheckAST :: (MonadError [Char] m, Synthable (a, LType)) => a -> TypeEnv -> m ()
typeCheckAST :: (MonadError String m) => Block -> TypeEnv -> m LType
typeCheckAST b = State.evalStateT (synth (b, Never))

-- Given AST and env, typechecks it, returning resulting store.
-- runForEnv :: (MonadError String m, MonadState TypeEnv m) => Block -> TypeEnv -> m TypeEnv
-- runForEnv b env = run (synth (b, Never)) env

-- case State.runStateT (synth (b, Never)) env of
-- (t, (_, finalStore)) -> return finalStore

-- (l, _) -> throwErr

-- throwError :: String -> LType -> Expression -> TypecheckerState a
-- throwError errorType expectedType exp = do
--   eActualType <- synthesis exp
--   env <- S.get
--   case eActualType of
--     Left error -> return $ Left error
--     Right actualType ->
--       return $
--         Left $
--           errorType
--             ++ ": expected type \
--                \["
--             ++ pretty expectedType
--             ++ "]\
--                \ got type ["
--             ++ pretty actualType
--             ++ "]"
--             ++ show env

-- | typeCheck blocks individually, with some state.
typeCheckBlocks :: (MonadError String m) => TypeEnv -> LType -> [Block] -> m LType
typeCheckBlocks env expectedReturnType = foldr checkBlock (return Never)
  where
    checkBlock :: (MonadError String m) => Block -> m LType -> m LType
    checkBlock b prevRes = do
      prevTT <- prevRes
      newT <- State.evalStateT (synth (b, expectedReturnType)) env
      return $ constructUnionType [prevTT, newT]

-- checkBlock b l@(Left _) = l
-- checkBlock b (Right prevT) = case S.evalState (synth (b, expectedReturnType)) env of
--   l@(Left _) -> l
--   Right nextT -> Right $ constructUnionType [prevT, nextT]

-- | Check that given expression is boolean, then check underlying blocks.
typeCheckConditionalBlocks :: (MonadError String m, MonadState TypeEnv m) => Expression -> LType -> [Block] -> String -> m LType
typeCheckConditionalBlocks exp expectedReturnType bs errorStr = do
  res <- checker exp BooleanType
  curStore <- State.get
  if res
    then typeCheckBlocks curStore expectedReturnType bs
    else throwError errorStr

-- case eRes of
--   Right True -> return $ typeCheckBlocks curStore expectedReturnType bs
--   _ -> return $ Left errorStr

typeCheckAssign :: (MonadError String m, MonadState TypeEnv m) => Var -> LType -> Expression -> m LType
typeCheckAssign v UnknownType exp = throwError ("Can not determine type of [" ++ pretty exp ++ "]")
typeCheckAssign v t exp = do
  res <- doTypeAssignment v t exp -- Do type assignment first, in case definition is recursive.
  sameType <- checker (Var v) t -- Check that variable updates to target type in case table key/value type changes.
  if sameType
    then return NilType
    else throwError "AssignmentError"

-- case (res, eSameType) of
--   (Left error, _) -> return $ Left error
--   (_, Left error) -> return $ Left error
--   (_, Right False) -> throwError "AssignmentError" t exp
--   (_, Right True) -> return $ Right NilType

-- Given var, its determined type, and
doTypeAssignment :: (MonadError String m, MonadState TypeEnv m) => Var -> LType -> Expression -> m ()
doTypeAssignment (Name n) tExpType exp = do
  (ref, curType :: LType) <- C.resolveName n
  if curType == NilType || curType == tExpType
    then updateRef ref tExpType exp
    else throwError "Cannot redefine variable to new type"
doTypeAssignment (Dot tExp n) vExpType exp = do
  tableType <- synthesis tExp
  typecheckTableAccess tableType StringType vExpType
  case tExp of
    (Var (Name tableName)) -> updateTableType tableName tableType StringType vExpType
    _ -> return ()
-- eTExpType <- synthesis tExp
-- case eTExpType of
--   Left l -> return $ Left l
--   Right tExpType -> case (typecheckTableAccess tExpType StringType vExpType, tExp) of
--     (Left l, _) -> return $ Left l
--     (Right _, Var (Name tableName)) -> updateTableType tableName tExpType StringType vExpType
--     (Right _, _) -> return $ Right ()
doTypeAssignment (Proj tExp kExp) vExpType exp = do
  keyType <- synthesis kExp
  tableType <- synthesis tExp
  case tExp of
    (Var (Name tableName)) -> updateTableType tableName tableType keyType vExpType
    _ -> return ()

-- eKExpType <- synthesis kExp
-- eTExpType <- synthesis tExp
-- case (eKExpType, eTExpType) of
--   (Left l, _) -> return $ Left l
--   (_, Left l) -> return $ Left l
--   (Right kExpType, Right tExpType) -> do
--     case (typecheckTableAccess tExpType kExpType vExpType, tExp) of
--       (Left l, _) -> return $ Left l
--       (Right _, Var (Name tableName)) -> updateTableType tableName tExpType kExpType vExpType
--       (Right _, _) -> return $ Right ()

-- | Check if accessing key with given type and expecting given type is valid for given table.
typecheckTableAccess :: (MonadError String m) => LType -> LType -> LType -> m ()
typecheckTableAccess (TableType kType vType) givenKType givenVType =
  if givenKType <: kType && givenVType <: vType
    then return ()
    else throwError "Table type sealed"
typecheckTableAccess _ _ _ = throwError "Unable to access value from non-table"

-- | Typecheck function body with current state, but don't allow it to affect current state.
preCheckFuncBody :: (MonadError String m, MonadState TypeEnv m) => Reference -> [Parameter] -> LType -> Block -> m ()
preCheckFuncBody ref pms rt b = do
  State.modify (addUncalledFunc ref (FunctionVal pms rt b))
  C.prepareFunctionEnv pms
  s <- State.get
  State.modify C.exitScope
  blockType <- State.evalStateT (synth (b, rt)) s
  if blockType <: rt
    then return ()
    else throwError $ "Expected block to return type " ++ show rt ++ " got type " ++ show blockType ++ " in body " ++ show b

-- return $ case blockType of
--   Left l -> Left l
--   Right actualType ->
--     if actualType <: rt
--       then Right ()
--       else Left $ "Expected block to return type " ++ show rt ++ " got type " ++ show actualType ++ " in body " ++ show b

-- | update key and value types associated with table in env.
updateTableType :: (MonadError String m, MonadState TypeEnv m) => Name -> LType -> LType -> LType -> m ()
updateTableType tableName (TableType kTypeOld vTypeOld) kTypeNew vTypeNew = do
  let kType = constructUnionType [kTypeOld, kTypeNew]
  let vType = constructUnionType [vTypeOld, vTypeNew]
  (ref, _ :: LType) <- C.resolveName tableName
  C.update ref (TableType kType vType)
  return ()
updateTableType _ _ _ _ = throwError "Cannot update non table."

checkSameType :: (MonadError String m, MonadState TypeEnv m) => Expression -> Expression -> m Bool
checkSameType e1 e2 = do
  t1 <- synthesis e1
  t2 <- synthesis e2
  return (t1 <: t2 && t2 <: t1)

-- case (eT1, eT2) of
--   (Right t1, Right t2) -> return $ Right (t1 <: t2 && t2 <: t1)
--   (Left error, _) -> return $ Left error
--   (_, Left error) -> return $ Left error

synthCall :: (MonadError String m, MonadState TypeEnv m) => LType -> [Expression] -> m LType
synthCall (FunctionType Never returnType) [] = return returnType
synthCall (FunctionType paramType returnType) (p : ps) = do
  let nextFunction = if null ps then FunctionType Never returnType else returnType
  sameType <- checker p paramType
  if sameType then synthCall nextFunction ps else throwError "Parameter Assignment"
-- case eRes of
--   (Left l) -> return l
--   Right False -> throwError "ParameterAssignment" paramType p
--   Right True -> synthCall nextFunction ps
synthCall t _ = throwError ("CallNonFunc: Cannot call type [" ++ show t ++ "]")

-- do
-- env <- State.get
-- return $ Left ("CallNonFunc: Cannot call type [" ++ show t ++ "]" ++ show env)

synthOp2 :: (MonadError String m, MonadState TypeEnv m) => Bop -> Expression -> Expression -> m LType
synthOp2 op e1 e2 = do
  opType <- synth op
  synthCall opType [e1, e2]

-- case eOpType of
--   Right opType -> synthCall opType [e1, e2]
--   (Left error) -> return $ Left error

synthOp2Poly :: (MonadError String m, MonadState TypeEnv m) => Bop -> Expression -> Expression -> m LType
synthOp2Poly op e1 e2 = do
  sameType <- checkSameType e1 e2
  if sameType then synthOp2 op e1 e2 else throwError "Recieved two different types in Op2 execution."

-- case eSameType of
--   Right False -> return $ Left "Recieved two different types in Op2 execution."
--   (Left error) -> return $ Left error
--   Right True -> synthOp2 op e1 e2

typeCheckFuncBody :: (MonadError String m, MonadState TypeEnv m) => Reference -> m ()
typeCheckFuncBody ref = do
  s <- State.get
  let funcValue = getUncalledFunc s ref
  case funcValue of
    Just (FunctionVal pms rt b) -> do
      C.prepareFunctionEnv pms
      State.modify (`removeUncalledFunc` ref)
      blockType <- synth (b, rt)
      State.modify C.exitScope
      if blockType <: rt
        then return ()
        else throwError $ "Return: expected type " ++ show rt ++ " but got type " ++ show blockType
    _ -> return ()

--   return $ case res of
--     Right t ->
--       if t <: rt
--         then return ()
--         else Left $ "Return: expected type " ++ show rt ++ " but got type " ++ show t
--     Left l -> Left l
-- _ -> return $ Right ()

isPolymorphicBop :: Bop -> Bool
isPolymorphicBop Eq = True
isPolymorphicBop Gt = True
isPolymorphicBop Ge = True
isPolymorphicBop Lt = True
isPolymorphicBop Le = True
isPolymorphicBop _ = False

synthesis :: (MonadError String m, MonadState TypeEnv m) => Expression -> m LType
synthesis (Op2 exp1 bop exp2) | isPolymorphicBop bop = synthOp2Poly bop exp1 exp2
synthesis (Op2 exp1 bop exp2) = synthOp2 bop exp1 exp2
synthesis (Val v) = synth v
synthesis (Var v) = synth v
synthesis (TableConst tfs) = synth tfs
synthesis (Call (Name n) pms) = do
  (ref, fType :: LType) <- C.resolveName n
  res <- synthCall fType pms
  bodyCheck <- typeCheckFuncBody ref
  return res
-- case fBodyCheck of
--   Left error -> return $ Left error
--   Right () -> return res
synthesis (Op1 uop exp) = do
  opType <- synth uop
  synthCall opType [exp]
-- case eOpType of
--   Right opType -> synthCall opType [exp]
--   l@(Left _) -> return l
synthesis (Call v pms) = undefined

checker :: (MonadError String m, MonadState TypeEnv m) => Expression -> LType -> m Bool
checker exp expectedType = do
  expType <- synthesis exp
  return $ expType <: expectedType

-- return $ case eType of
--   Left l -> Left l
--   Right actualType -> Right $ actualType <: expectedType

runSynthesis :: TypeEnv -> Expression -> LType
runSynthesis env exp = case runExceptT $ State.evalStateT (synthesis exp) env of
  Right (Right v) -> v
  _ -> UnknownType

-- | Check that type of given expression is an instance of given type.
runChecker :: TypeEnv -> Expression -> LType -> Bool
runChecker env e = (<:) (runSynthesis env e)

runForType :: StateT s (ExceptT e (Either a)) LType -> s -> LType -> LType
runForType p env fail = case runExceptT (State.evalStateT p env) of
  Right (Right v) -> v
  _ -> fail

runForEnv :: (Synthable (a, LType)) => a -> TypeEnv -> Either String TypeEnv
runForEnv b env = runExcept $ State.execStateT (synth (b, Never)) env