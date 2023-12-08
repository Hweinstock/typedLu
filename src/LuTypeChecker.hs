module LuTypeChecker where

import Control.Monad
import LuSyntax
import State (State)
import qualified State as S
import Data.Map (Map)
import Data.List (nub)
import qualified Data.Map as Map
import Stack (Stack)
import qualified Stack
import LuTypes 

-- newtype EitherT m a = EitherT { runEitherT :: m (Either String a) }

-- instance Monad m => Monad (EitherT m) where 
--     return :: a -> EitherT m a
--     return = pure 
--     (>>=) = bind where 
--         bind :: EitherT m a -> (a -> EitherT m b) -> EitherT m b
--         bind x f = EitherT $ do 
--             eitherValue <- runEitherT x 
--             case eitherValue of 
--                 Left s -> return $ Left s
--                 Right v -> runEitherT $ f v

-- instance Monad m => Applicative (EitherT m) where
--     pure = EitherT . return . Right
--     (<*>) = ap

-- instance Monad m => Functor (EitherT m) where
--     fmap = liftM

returnTypeName :: Name 
returnTypeName = "@R"

{- 
When we see a local variable, add it to the stack. 
When we want to access a local varaible, we sift through the stack until we find matching name, 
then we use that name

-}


data Environment = Environment {
    gTypeMap :: Map Name LType,
    localStack :: Stack LocalVar,
    functionMap :: Map Name Value, 
    curDepth :: Int
}

data LocalVar = LocalVar {
    lType :: LType,
    name :: Name,
    depth :: Int
}

instance Show LocalVar where 
    show :: LocalVar -> String 
    show lv = show (name lv) ++ "=" ++ show (lType lv) ++ ":" ++ show (depth lv)


instance Show Environment where 
    show :: Environment -> String 
    show env = show (gTypeMap env) ++ "\n" ++ show (localStack env) ++ "\n" ++ show (functionMap env) ++ "[depth=" ++ show (curDepth env) ++ "]"

emptyStore :: Environment 
emptyStore = Environment {gTypeMap = Map.empty, functionMap = Map.empty, localStack = Stack.empty, curDepth = 0}

addGTypeToEnv :: (Name, LType) -> Environment -> Environment
addGTypeToEnv (k, v) env = env {gTypeMap = Map.insert k v (gTypeMap env)}

addLTypeToEnv :: (Name, LType) -> Environment -> Environment
addLTypeToEnv (n, t) env = env {localStack = Stack.push (localStack env) lv} where 
    lv = LocalVar {lType = t, name = n, depth = curDepth env}

addFuncToEnv :: (Name, Value) -> Environment -> Environment
addFuncToEnv (k, v) env = env {functionMap = Map.insert k v (functionMap env)}

getGTypeFromEnv :: Environment -> Name -> Maybe LType 
getGTypeFromEnv env n = Map.lookup n (gTypeMap env)

getLTypeFromEnv :: Environment -> Name -> Maybe LType 
getLTypeFromEnv env n = case Stack.peekUntil (localStack env) (\lv -> name lv == n) of 
    Just lv -> Just $ lType lv 
    _ -> Nothing

getTypeFromEnv :: Environment -> Name -> Maybe LType 
getTypeFromEnv env n = case (getGTypeFromEnv env n, getLTypeFromEnv env n) of 
    (_, Just t) -> Just t
    (Just t, _) -> Just t 
    _ -> Nothing

lookupType :: Name -> State Environment (Maybe LType) 
lookupType n = S.get >>= \env -> return $ getTypeFromEnv env n

getFuncFromEnv :: Environment -> Name -> Maybe Value 
getFuncFromEnv env n = Map.lookup n (functionMap env)

removeFuncFromEnv :: Environment -> Name -> Environment 
removeFuncFromEnv env n = env {functionMap = Map.delete n (functionMap env)}

-- | Decrease depth of scope and remove variables at this level. 
exitScope :: Environment -> Environment 
exitScope env = env {localStack = Stack.popUntil (localStack env) (aboveDepth (curDepth env)), curDepth = curDepth env - 1} where 
    aboveDepth :: Int -> LocalVar -> Bool 
    aboveDepth n lv = depth lv < curDepth env

-- | Increase depth of scope. 
enterScope :: Environment -> Environment 
enterScope env = env {curDepth = curDepth env + 1}

-- type TypecheckerState = EitherT (State EnvironmentTypes) ()  -- transformer version

type TypecheckerState a = State Environment (Either String a)

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
    synth (TableVal n) = undefined --what is this case? 
    synth (FunctionVal pms rt b) = do 
        prepareFunctionEnv pms rt 
        s <- S.get
        S.modify exitScope
        case S.evalState (typeCheckBlock b) s of 
            Right () -> do 
                return $ Right $ synthFunc pms rt
            Left l -> return $ Left l

synthFunc :: [Parameter] -> LType -> LType 
synthFunc [] rt = FunctionType Never rt 
synthFunc [(_, t)] rt = FunctionType t rt
synthFunc ((_, t) : ps) rt = FunctionType t (synthFunc ps rt)

instance Synthable Var where 
    synth (Name n) = do 
        mT <- lookupType n 
        case mT of 
            Just t -> return $ Right t
            _ -> return $ Right NilType
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

prepareFunctionEnv :: [Parameter] -> LType -> State Environment ()
prepareFunctionEnv pms rt = S.modify enterScope >> S.modify (\e -> foldr addLTypeToEnv e ((returnTypeName, rt) : pms))

isPolymorphicBop :: Bop -> Bool
isPolymorphicBop Eq = True 
isPolymorphicBop Gt = True 
isPolymorphicBop Ge = True 
isPolymorphicBop Lt = True 
isPolymorphicBop Le = True 
isPolymorphicBop _ = False 

typeCheckAST :: Block -> Either String () 
typeCheckAST b = S.evalState (typeCheckBlock b) emptyStore

getTypeEnv :: Block -> Either String Environment 
getTypeEnv b = case S.runState (typeCheckBlock b) emptyStore of 
    (Right (), finalStore) -> Right finalStore
    (Left l, finalStore) -> Left l
    
throwError :: String -> LType -> Expression -> TypecheckerState a 
throwError errorType expectedType exp = do 
    eActualType <- synthesis exp 
    curStore <- S.get
    case eActualType of 
        Left error -> return $ Left error 
        Right actualType -> return $ Left $  
            errorType ++ ": expected type \
            \[" ++ pretty expectedType ++ "]\
            \ got type [" ++ pretty actualType ++ "]\
            \" ++ show curStore


-- | typeCheck blocks individually, with some state. 
typeCheckBlocks :: Environment -> [Block] -> Either String ()
typeCheckBlocks env = foldr checkBlock (Right ()) where 
    checkBlock :: Block -> Either String () -> Either String () 
    checkBlock b l@(Left _) = l 
    checkBlock b _ = S.evalState (typeCheckBlock b) env
    
-- | Check that given expression is boolean, then check underlying blocks.
typeCheckCondtionalBlocks :: Expression -> [Block] -> String -> TypecheckerState ()
typeCheckCondtionalBlocks exp bs errorStr = do 
    eRes <- checker exp BooleanType
    curStore <- S.get
    case eRes of 
        Right True -> return $ typeCheckBlocks curStore bs
        _ -> return $ Left errorStr

-- | Given a block and an environment, check if the types are consistent in the block. 
typeCheckBlock :: Block -> TypecheckerState ()
typeCheckBlock (Block (s : ss)) = do 
    curCheck <- typeCheckStatement s 
    case curCheck of 
        l@(Left _) -> return l 
        Right () -> typeCheckBlock (Block ss)
typeCheckBlock (Block []) = return $ Right ()

-- | Given a statement and an environment, check if the types are consistent in the statement. 
typeCheckStatement :: Statement -> TypecheckerState ()
typeCheckStatement (Assign (v, UnknownType) exp) = do 
    eTexp <- synthesis exp 
    case eTexp of 
        Right t -> typeCheckAssign v t exp 
        Left l -> return $ Left l 
typeCheckStatement (Assign (v, t) exp) = typeCheckAssign v t exp
typeCheckStatement (If exp b1 b2) = typeCheckCondtionalBlocks exp [b1, b2] "Non-boolean in if condition"
typeCheckStatement (While exp b) = typeCheckCondtionalBlocks exp [b] "Non-boolean in while condition"
typeCheckStatement Empty = return $ Right ()  
typeCheckStatement (Repeat b exp) = typeCheckCondtionalBlocks exp [b] "Non-boolean in repeat condition"
typeCheckStatement (Return exp) = do 
    eExpectedType <- synth (Name returnTypeName)
    case eExpectedType of 
        Left error -> return $ Left error
        Right expectedType -> do 
            eRes <- checker exp expectedType 
            case eRes of 
                Left error -> return $ Left error 
                Right False -> throwError "Return:" expectedType exp 
                Right True -> return $ Right () 

typeCheckAssign :: Var -> LType -> Expression -> TypecheckerState ()
typeCheckAssign v UnknownType exp = return $ Left ("Can not determine type of [" ++ pretty exp ++ "]")
typeCheckAssign v t exp = do 
    doTypeAssignment v t exp -- Try to do type assignment, then evaluate expression type. (Recursive definitions)
    eSameType <- checker exp t 
    case eSameType of 
        Left error -> return $ Left error 
        Right False -> throwError "AssignmentError" t exp
        Right True -> return $ Right ()
    
doTypeAssignment ::  Var -> LType -> Expression -> TypecheckerState ()
doTypeAssignment (Name n) tExpType exp = do 
    eCurrentType <- synth (Name n)
    case eCurrentType of 
        Left l -> return $ Left l
        Right NilType -> updateEnv n tExpType exp
        Right UnknownType -> return $ Left "Unable to determine type of expression in assignment"
        Right curType -> if curType /= tExpType then 
            return $ Left "Cannot redefine variable to new type"
            else updateEnv n tExpType exp
doTypeAssignment (Dot tExp n) vExpType _ = do 
    eTExpType <- synthesis tExp 
    return $ case eTExpType of 
        Left l -> Left l 
        Right tExpType -> typecheckTableAccess tExpType StringType vExpType
doTypeAssignment (Proj tExp kExp) vExpType _ = do 
    eKExpType <- synthesis kExp
    eTExpType <- synthesis tExp
    return $ case (eKExpType, eTExpType) of 
        (Right kExpType, Right tExpType) -> typecheckTableAccess tExpType kExpType vExpType
        (Left l, _) -> Left l 
        (_, Left l) -> Left l

typecheckTableAccess :: LType -> LType -> LType -> Either String ()
typecheckTableAccess (TableType kType vType) givenKType givenVType = 
    if givenKType <: kType && givenVType <: vType 
        then Right () 
        else Left "Table type sealed"
typecheckTableAccess _ _ _= Left "Unable to access value from non-table"

-- | Update variable type in store. 
updateEnv :: Name -> LType -> Expression -> TypecheckerState ()
updateEnv n t exp = do 
    env <- S.get 
    S.modify (addGTypeToEnv (n, t))
    case (t, exp) of 
        (FunctionType _ _, Val f) -> do 
            S.modify (addFuncToEnv (n, f))
            return $ Right () 
        _ -> return $ Right ()

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
synthCall t _ = return $ Left ("CallNonFunc: Cannot call type [" ++ show t ++ "]")

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

typeCheckFuncBody :: Name -> TypecheckerState () 
typeCheckFuncBody n = do 
    s <- S.get 
    let funcValue = getFuncFromEnv s n  
    case funcValue of 
        Just (FunctionVal pms rt b) -> do 
            prepareFunctionEnv pms rt 
            S.modify (\env -> removeFuncFromEnv env n)
            res <- typeCheckBlock b 
            S.modify exitScope 
            return res
        _ -> return $ Right ()

synthesis :: Expression -> TypecheckerState LType  
synthesis (Call (Name n) pms) = do 
    eFType <- synth (Name n) 
    case eFType of 
        Left error -> return $ Left error 
        Right fType -> do 
            let res = synthCall fType pms
            fBodyCheck <- typeCheckFuncBody n 
            case fBodyCheck of 
                Left error -> return $ Left error
                Right () -> res
    
    
    -- do 
    -- functionBodyCheck <- typeCheckFuncBody n
    -- case functionBodyCheck of 
    --     Left l -> return $ Left ("Undefined: Undefined function " ++ n ++ " being called.")
    --     Right () -> do 
    --         eFType <- synth (Name n)
    --         case eFType of 
    --             Right fType -> synthCall fType pms 
    --             Left error -> return $ Left error
synthesis (Op1 uop exp) = do 
    eOpType <- synth uop
    case eOpType of 
        Right opType -> synthCall opType [exp]
        l@(Left _) -> return l
synthesis (Op2 exp1 bop exp2) | isPolymorphicBop bop = synthOp2Poly bop exp1 exp2   
synthesis (Op2 exp1 bop exp2) = synthOp2 bop exp1 exp2
synthesis (Val v) = synth v
synthesis (Var v) = synth v
synthesis (TableConst tfs) = synth tfs  

checker :: Expression -> LType -> TypecheckerState Bool 
checker exp expectedType = do 
    eType <- synthesis exp 
    return $ case eType of 
        Left l -> Left l
        Right actualType -> Right $ actualType <: expectedType

runSynthesis :: Environment -> Expression -> LType 
runSynthesis env exp = case S.evalState (synthesis exp) env of 
    Right t -> t 
    Left _ -> UnknownType

-- | Check that type of given expression is an instance of given type. 
runChecker :: Environment -> Expression -> LType -> Bool
runChecker env e = (<:) (runSynthesis env e)

