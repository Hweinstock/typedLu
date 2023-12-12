module LuTypeChecker where

import Context (Context, Environment, ExtendedContext, Reference (GlobalRef, LocalRef, TableRef))
import Context qualified as C
import Control.Monad
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

  index :: Reference -> State TypeEnv LType
  index r@(GlobalRef _) = C.indexWithDefault r NilType
  index r@(LocalRef _) = C.indexWithDefault r UnknownType
  index r = C.indexWithDefault r NilType

  indexTable :: (Name, Value) -> LType -> State TypeEnv LType
  indexTable _ = return

  updateTable :: (Name, Value) -> LType -> State TypeEnv ()
  updateTable _ _ = return ()

  lookup :: Name -> State TypeEnv LType
  lookup = C.lookupWithUnknown UnknownType

  resolve :: Name -> State TypeEnv (Reference, LType)
  resolve = C.resolveWithUnknown UnknownType

emptyTypeEnv :: TypeEnv
emptyTypeEnv = TypeEnv {context = C.emptyContext, uncalledFuncs = Map.empty}

addUncalledFunc :: Reference -> Value -> TypeEnv -> TypeEnv
addUncalledFunc ref v env = env {uncalledFuncs = Map.insert ref v (uncalledFuncs env)}

getUncalledFunc :: TypeEnv -> Reference -> Maybe Value
getUncalledFunc env n = Map.lookup n (uncalledFuncs env)

removeUncalledFunc :: TypeEnv -> Reference -> TypeEnv
removeUncalledFunc env n = env {uncalledFuncs = Map.delete n (uncalledFuncs env)}

type TypecheckerState a = State TypeEnv (Either String a)

class Synthable a where
  synth :: a -> TypecheckerState LType

instance Synthable Uop where
  synth Neg = return $ return $ FunctionType IntType IntType
  synth Not = return $ return $ FunctionType AnyType BooleanType
  synth Len = return $ return $ FunctionType (UnionType IntType (UnionType StringType (TableType AnyType AnyType))) IntType

instance Synthable Bop where
  synth Plus = return $ return $ FunctionType IntType (FunctionType IntType IntType)
  synth Minus = return $ return $ FunctionType IntType (FunctionType IntType IntType)
  synth Times = return $ return $ FunctionType IntType (FunctionType IntType IntType)
  synth Divide = return $ return $ FunctionType IntType (FunctionType IntType IntType)
  synth Modulo = return $ return $ FunctionType IntType (FunctionType IntType IntType)
  synth Eq = return $ return $ FunctionType AnyType (FunctionType AnyType BooleanType)
  synth Gt = return $ return $ FunctionType AnyType (FunctionType AnyType BooleanType)
  synth Ge = return $ return $ FunctionType AnyType (FunctionType AnyType BooleanType)
  synth Lt = return $ return $ FunctionType AnyType (FunctionType AnyType BooleanType)
  synth Le = return $ return $ FunctionType AnyType (FunctionType AnyType BooleanType)
  synth Concat = return $ return $ FunctionType StringType (FunctionType StringType StringType)

instance Synthable Value where
  synth NilVal = return $ return NilType
  synth (IntVal _) = return $ return IntType
  synth (BoolVal _) = return $ return BooleanType
  synth (StringVal _) = return $ return StringType
  synth (TableVal n) = undefined -- what is this case?
  synth (ErrorVal _) = return $ return NilType -- shouldn't hit this case.
  synth (FunctionVal pms rt b) = do
    return $ Right $ synthFunc pms rt
    where
      synthFunc :: [Parameter] -> LType -> LType
      synthFunc [] rt = FunctionType Never rt
      synthFunc [(_, t)] rt = FunctionType t rt
      synthFunc ((_, t) : ps) rt = FunctionType t (synthFunc ps rt)

instance Synthable Var where
  synth (Name n) = Right <$> C.lookup n
  synth (Dot exp n) = do
    eExpType <- synthesis exp
    return $ case eExpType of
      Left l -> Left l
      Right tExp@(TableType t1 t2) -> case typecheckTableAccess tExp StringType Never of
        Right () -> Right t2
        Left l -> Left l
      Right _ -> Left "Cannot access non table type via dot method."
  synth (Proj tExp kExp) = do
    eTableType <- synthesis tExp
    eKeyType <- synthesis kExp
    return $ case (eTableType, eKeyType) of
      (Left l, _) -> Left l
      (_, Left l) -> Left l
      (Right tableType@(TableType t1 t2), Right keyType) -> case typecheckTableAccess tableType keyType Never of
        Right () -> Right t2
        Left l -> Left l
      _ -> Left "Cannot access not table type via proj method."

instance Synthable [TableField] where
  synth tfs = do
    eTypePairs <- foldr synthTableField (return $ Right []) tfs
    return $ case eTypePairs of
      Left l -> Left l
      Right typePairs -> do
        let (keyTypes, valTypes) = unzip typePairs
        Right $ TableType (constructUnionType keyTypes) (constructUnionType valTypes)
    where
      synthTableField :: TableField -> TypecheckerState [(LType, LType)] -> TypecheckerState [(LType, LType)]
      synthTableField (FieldName n e) res = synthTableField (FieldKey (Val (StringVal n)) e) res
      synthTableField (FieldKey e1 e2) res = do
        ePairs <- res
        eT1 <- synthesis e1
        eT2 <- synthesis e2
        case (ePairs, eT1, eT2) of
          (Right pairs, Right t1, Right t2) -> return $ Right ((t1, t2) : pairs)
          (Left l, _, _) -> return $ Left l
          (_, Left l, _) -> return $ Left l
          (_, _, Left l) -> return $ Left l

instance Synthable (Statement, LType) where
  -- \| Given a statement, an environment and an expected return type, check if the types are consistent in the statement.
  synth :: (Statement, LType) -> TypecheckerState LType
  synth (Assign (v, UnknownType) exp, expectedReturnType) = do
    eTexp <- synthesis exp
    case eTexp of
      Right t -> typeCheckAssign v t exp
      Left l -> return $ Left l
  synth (Assign (v, t) exp, expectedReturnType) = typeCheckAssign v t exp
  synth (If exp b1 b2, expectedReturnType) = typeCheckCondtionalBlocks exp expectedReturnType [b1, b2] "Non-boolean in if condition"
  synth (While exp b, expectedReturnType) = typeCheckCondtionalBlocks exp expectedReturnType [b] "Non-boolean in while condition"
  synth (Empty, expectedReturnType) = return $ Right NilType
  synth (Repeat b exp, expectedReturnType) = typeCheckCondtionalBlocks exp expectedReturnType [b] "Non-boolean in repeat condition"
  synth (Return exp, expectedReturnType) = do
    eRes <- checker exp expectedReturnType
    case eRes of
      Left error -> return $ Left error
      Right False -> throwError "Return" expectedReturnType exp
      Right True -> return $ Right expectedReturnType

instance Synthable (Block, LType) where
  -- \| Given a block, an environment, and an expected return type, return the type returned by the block.
  synth :: (Block, LType) -> TypecheckerState LType
  synth (Block [s], expectedReturnType) = synth (s, expectedReturnType)
  synth (Block (s : ss), expectedReturnType) = do
    curCheck <- synth (s, expectedReturnType)
    case (s, curCheck) of
      (_, Left l) -> return $ Left l
      (Return exp, Right t) -> do
        eRes <- checker exp t
        case eRes of
          Left l -> return $ Left l
          Right False -> throwError "BlockType" expectedReturnType exp
          Right True -> return $ Right t
      (_, Right t) -> synth (Block ss, expectedReturnType)
  synth (Block [], expectedReturnType) = return $ Right NilType

isPolymorphicBop :: Bop -> Bool
isPolymorphicBop Eq = True
isPolymorphicBop Gt = True
isPolymorphicBop Ge = True
isPolymorphicBop Lt = True
isPolymorphicBop Le = True
isPolymorphicBop _ = False

typeCheckAST :: Block -> TypeEnv -> Either String ()
typeCheckAST b env = case S.evalState (synth (b, Never)) env of
  Right t -> Right ()
  Left l -> Left l

runForEnv :: Block -> TypeEnv -> Either String TypeEnv
runForEnv b env = case S.runState (synth (b, Never)) env of
  (Right t, finalStore) -> Right finalStore
  (Left l, finalStore) -> Left l

throwError :: String -> LType -> Expression -> TypecheckerState a
throwError errorType expectedType exp = do
  eActualType <- synthesis exp
  env <- S.get
  case eActualType of
    Left error -> return $ Left error
    Right actualType ->
      return $
        Left $
          errorType
            ++ ": expected type \
               \["
            ++ pretty expectedType
            ++ "]\
               \ got type ["
            ++ pretty actualType
            ++ "]"
            ++ show env

-- | typeCheck blocks individually, with some state.
typeCheckBlocks :: TypeEnv -> LType -> [Block] -> Either String LType
typeCheckBlocks env expectedReturnType = foldr checkBlock (Right Never)
  where
    checkBlock :: Block -> Either String LType -> Either String LType
    checkBlock b l@(Left _) = l
    checkBlock b (Right prevT) = case S.evalState (synth (b, expectedReturnType)) env of
      l@(Left _) -> l
      Right nextT -> Right $ constructUnionType [prevT, nextT]

-- | Check that given expression is boolean, then check underlying blocks.
typeCheckCondtionalBlocks :: Expression -> LType -> [Block] -> String -> TypecheckerState LType
typeCheckCondtionalBlocks exp expectedReturnType bs errorStr = do
  eRes <- checker exp BooleanType
  curStore <- S.get
  case eRes of
    Right True -> return $ typeCheckBlocks curStore expectedReturnType bs
    _ -> return $ Left errorStr

typeCheckAssign :: Var -> LType -> Expression -> TypecheckerState LType
typeCheckAssign v UnknownType exp = return $ Left ("Can not determine type of [" ++ pretty exp ++ "]")
typeCheckAssign v t exp = do
  res <- doTypeAssignment v t exp -- Try to do type assignment, then evaluate expression type. (Recursive definitions)
  eSameType <- checker (Var v) t -- check that variable updates to target type.
  case (res, eSameType) of
    (Left error, _) -> return $ Left error
    (_, Left error) -> return $ Left error
    (_, Right False) -> throwError "AssignmentError" t exp
    (_, Right True) -> return $ Right NilType

-- TODO: Cleanup.
doTypeAssignment :: Var -> LType -> Expression -> TypecheckerState ()
doTypeAssignment (Name n) tExpType exp = do
  (ref, curType :: LType) <- C.resolve n
  if curType == NilType || curType == tExpType
    then updateEnv ref tExpType exp
    else return $ Left "Cannot redefine variable to new type"
doTypeAssignment (Dot e@(Var (Name tableName)) n) vExpType exp = do
  eTExpType <- synthesis e
  case eTExpType of
    Left l -> return $ Left l
    Right tExpType -> do
      case typecheckTableAccess tExpType StringType vExpType of
        Left l -> return $ Left l
        Right l -> updateTableType tableName tExpType StringType vExpType
doTypeAssignment (Dot tExp n) vExpType _ = do
  eTExpType <- synthesis tExp
  return $ case eTExpType of
    Left l -> Left l
    Right tExpType -> typecheckTableAccess tExpType StringType vExpType
doTypeAssignment (Proj e@(Var (Name tableName)) kExp) vExpType exp = do
  eKExpType <- synthesis kExp
  eTExpType <- synthesis e
  case (eTExpType, eKExpType) of
    (Left l, _) -> return $ Left l
    (_, Left l) -> return $ Left l
    (Right tExpType, Right kExpType) -> do
      case typecheckTableAccess tExpType kExpType vExpType of
        Left l -> return $ Left l
        Right l -> updateTableType tableName tExpType kExpType vExpType
doTypeAssignment (Proj tExp kExp) vExpType _ = do
  eKExpType <- synthesis kExp
  eTExpType <- synthesis tExp
  return $ case (eKExpType, eTExpType) of
    (Right kExpType, Right tExpType) -> typecheckTableAccess tExpType kExpType vExpType
    (Left l, _) -> Left l
    (_, Left l) -> Left l

-- | Check if accessing key with given type and expecting given type is valid for given table.
typecheckTableAccess :: LType -> LType -> LType -> Either String ()
typecheckTableAccess (TableType kType vType) givenKType givenVType =
  if givenKType <: kType && givenVType <: vType
    then Right ()
    else Left "Table type sealed"
typecheckTableAccess _ _ _ = Left "Unable to access value from non-table"

-- | Update variable type in store.
updateEnv :: Reference -> LType -> Expression -> TypecheckerState ()
updateEnv ref t exp = do
  C.update ref t
  case (t, exp) of
    (FunctionType _ _, Val f@(FunctionVal pms rt b)) -> preCheckFuncBody ref pms rt b
    _ -> return $ Right ()

-- | Typecheck function body with current state, but don't allow it to affect current state.
preCheckFuncBody :: Reference -> [Parameter] -> LType -> Block -> TypecheckerState ()
preCheckFuncBody ref pms rt b = do
  S.modify (addUncalledFunc ref (FunctionVal pms rt b))
  C.prepareFunctionEnv pms
  s <- S.get
  S.modify C.exitScope
  let blockType = S.evalState (synth (b, rt)) s
  return $ case blockType of
    Left l -> Left l
    Right actualType ->
      if actualType <: rt
        then Right ()
        else Left $ "Expected block to return type " ++ show rt ++ " got type " ++ show actualType ++ " in body " ++ show b

updateTableType :: Name -> LType -> LType -> LType -> TypecheckerState ()
updateTableType tableName (TableType kTypeOld vTypeOld) kTypeNew vTypeNew = do
  let kType = constructUnionType [kTypeOld, kTypeNew]
  let vType = constructUnionType [vTypeOld, vTypeNew]
  (ref, _ :: LType) <- C.resolve tableName
  C.update ref (TableType kType vType)
  return $ Right ()
updateTableType _ _ _ _ = return $ Left "Cannot update non table."

checkSameType :: Expression -> Expression -> TypecheckerState Bool
checkSameType e1 e2 = do
  eT1 <- synthesis e1
  eT2 <- synthesis e2
  case (eT1, eT2) of
    (Right t1, Right t2) -> return $ Right (t1 <: t2 && t2 <: t1)
    (Left error, _) -> return $ Left error
    (_, Left error) -> return $ Left error

synthCall :: LType -> [Expression] -> TypecheckerState LType
synthCall (FunctionType Never returnType) [] = return $ Right returnType
synthCall (FunctionType paramType returnType) (p : ps) = do
  let nextFunction = if null ps then FunctionType Never returnType else returnType
  eRes <- checker p paramType
  case eRes of
    (Left l) -> return $ Left l
    Right False -> throwError "ParameterAssignment" paramType p
    Right True -> synthCall nextFunction ps
synthCall t _ = do
  env <- S.get
  return $ Left ("CallNonFunc: Cannot call type [" ++ show t ++ "]" ++ show env)

synthOp2 :: Bop -> Expression -> Expression -> TypecheckerState LType
synthOp2 op e1 e2 = do
  eOpType <- synth op
  case eOpType of
    Right opType -> synthCall opType [e1, e2]
    (Left error) -> return $ Left error

synthOp2Poly :: Bop -> Expression -> Expression -> TypecheckerState LType
synthOp2Poly op e1 e2 = do
  eSameType <- checkSameType e1 e2
  case eSameType of
    Right False -> return $ Left "Recieved two different types in Op2 execution."
    (Left error) -> return $ Left error
    Right True -> synthOp2 op e1 e2

typeCheckFuncBody :: Reference -> TypecheckerState ()
typeCheckFuncBody ref = do
  s <- S.get
  let funcValue = getUncalledFunc s ref
  case funcValue of
    Just (FunctionVal pms rt b) -> do
      C.prepareFunctionEnv pms
      S.modify (`removeUncalledFunc` ref)
      res <- synth (b, rt)
      S.modify C.exitScope
      return $ case res of
        Right t ->
          if t <: rt
            then return ()
            else Left $ "Return: expected type " ++ show rt ++ " but got type " ++ show t
        Left l -> Left l
    _ -> return $ Right ()

synthesis :: Expression -> TypecheckerState LType
synthesis (Op2 exp1 bop exp2) | isPolymorphicBop bop = synthOp2Poly bop exp1 exp2
synthesis (Op2 exp1 bop exp2) = synthOp2 bop exp1 exp2
synthesis (Val v) = synth v
synthesis (Var v) = synth v
synthesis (TableConst tfs) = synth tfs
synthesis (Call (Name n) pms) = do
  (ref, fType :: LType) <- C.resolve n
  res <- synthCall fType pms
  fBodyCheck <- typeCheckFuncBody ref
  case fBodyCheck of
    Left error -> return $ Left error
    Right () -> return res
synthesis (Op1 uop exp) = do
  eOpType <- synth uop
  case eOpType of
    Right opType -> synthCall opType [exp]
    l@(Left _) -> return l
synthesis (Call v pms) = undefined

checker :: Expression -> LType -> TypecheckerState Bool
checker exp expectedType = do
  eType <- synthesis exp
  return $ case eType of
    Left l -> Left l
    Right actualType -> Right $ actualType <: expectedType

runSynthesis :: TypeEnv -> Expression -> LType
runSynthesis env exp = case S.evalState (synthesis exp) env of
  Right t -> t
  Left _ -> UnknownType

-- | Check that type of given expression is an instance of given type.
runChecker :: TypeEnv -> Expression -> LType -> Bool
runChecker env e = (<:) (runSynthesis env e)