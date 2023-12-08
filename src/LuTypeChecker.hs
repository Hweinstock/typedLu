module LuTypeChecker where

import Control.Monad
import LuSyntax
import State (State)
import qualified State as S
import Data.Map (Map)
import Data.List (nub)
import qualified Data.Map as Map
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

getReturnTypeName :: State Environment Name 
getReturnTypeName = do 
    env <- S.get 
    return (returnTypeName ++ show (curDepth env))

data Environment = Environment {
    gTypeMap :: Map Name LType,
    lTypeMap :: Map Name LocalVar,
    functionMap :: Map Name Value, 
    curDepth :: Int
}

data LocalVar = LocalVar {
    lType :: LType,
    depth :: Int
}

instance Show LocalVar where 
    show :: LocalVar -> String 
    show lv = show (lType lv) ++ ":" ++ show (depth lv)


instance Show Environment where 
    show :: Environment -> String 
    show env = show (gTypeMap env) ++ "\n" ++ show (lTypeMap env) ++ "\n" ++ show (functionMap env) 

emptyStore :: Environment 
emptyStore = Environment {gTypeMap = Map.empty, functionMap = Map.empty, lTypeMap = Map.empty, curDepth = 0}

addGTypeToEnv :: (Name, LType) -> Environment -> Environment
addGTypeToEnv (k, v) env = env {gTypeMap = Map.insert k v (gTypeMap env)}

addLTypeToEnv :: (Name, LType) -> Environment -> Environment
addLTypeToEnv (k, v) env = env {lTypeMap = Map.insert k lv (lTypeMap env)} where 
    lv = LocalVar {lType = v, depth = curDepth env}

addFuncToEnv :: (Name, Value) -> Environment -> Environment
addFuncToEnv (k, v) env = env {functionMap = Map.insert k v (functionMap env)}

getGTypeFromEnv :: Environment -> Name -> Maybe LType 
getGTypeFromEnv env n = Map.lookup n (gTypeMap env)

getLTypeFromEnv :: Environment -> Name -> Maybe LType 
getLTypeFromEnv env n = Map.lookup n (lTypeMap env) >>= \m -> return (lType m)

getTypeFromEnv :: Environment -> Name -> Maybe LType 
getTypeFromEnv env n = case (getGTypeFromEnv env n, getLTypeFromEnv env n) of 
    (_, Just t) -> Just t
    (Just t, _) -> Just t 
    _ -> Nothing

getFuncFromEnv :: Environment -> Name -> Maybe Value 
getFuncFromEnv env n = Map.lookup n (functionMap env)

removeFuncFromEnv :: Environment -> Name -> Environment 
removeFuncFromEnv env n = env {functionMap = Map.delete n (functionMap env)}

-- | Decrease depth of scope and remove variables at this level. 
exitScope :: Environment -> Environment 
exitScope env = env {lTypeMap = newLocalMap, curDepth = curDepth env - 1} where 
    newLocalMap :: Map Name LocalVar 
    newLocalMap = Map.filter (\v -> depth v /= curDepth env) (lTypeMap env)

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
        case S.evalState (typeCheckBlock b) s of 
            Right () -> do 
                S.modify exitScope
                return $ Right $ synthFunc pms rt
            Left l -> return $ Left l
            where 
                synthFunc :: [Parameter] -> LType -> LType 
                synthFunc [] rt = FunctionType Never rt 
                synthFunc [(_, t)] rt = FunctionType t rt
                synthFunc ((_, t) : ps) rt = FunctionType t (synthFunc ps rt)

instance Synthable Var where 
    synth (Name n) = do 
        s <- S.get 
        case getTypeFromEnv s n of 
            Just t -> return $ Right t 
            _ -> return $ Right NilType
    synth (Dot exp n) = do 
        eTExp <- synthesis exp 
        return $ case eTExp of 
            Left l -> Left l 
            Right tExp@(TableType t1 t2) -> case typecheckTableAccess tExp StringType Never of 
                Right () -> Right t2 
                Left l -> Left l
            Right _ -> Left "Cannot access not table type via dot method."

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
                Right $ TableType (constructType keyTypes) (constructType valTypes)
        
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

        constructType :: [LType] -> LType 
        constructType = foldr constructTypeHelper UnknownType where 
            constructTypeHelper :: LType -> LType -> LType 
            constructTypeHelper t1 UnknownType = t1
            constructTypeHelper t1 accT | t1 <: accT = accT 
            constructTypeHelper t1 accT | accT <: t1 = t1 
            constructTypeHelper t1 accT = UnionType t1 accT

prepareFunctionEnv :: [Parameter] -> LType -> State Environment ()
prepareFunctionEnv pms rt = do 
    S.modify enterScope
    curRtName <- getReturnTypeName
    S.modify (\e -> foldr addLTypeToEnv e ((curRtName, rt) : pms))

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
    
-- | Generate error message with a type, expected type, and actual type. 
errorMsg :: String -> LType -> LType -> String 
errorMsg errorType expectedType actualType = 
    errorType ++ ": expected type [" ++ pretty expectedType ++ "] got type [" ++ pretty actualType ++ "]" 

-- | typeCheck blocks individually, with some state. 
typeCheckBlocks :: Environment -> [Block] -> Either String ()
typeCheckBlocks env = foldr checkBlock (Right ()) where 
    checkBlock :: Block -> Either String () -> Either String () 
    checkBlock b l@(Left _) = l 
    checkBlock b _ = S.evalState (typeCheckBlock b) env
    
-- | Check that given expression is boolean, then check underlying blocks.
typeCheckCondtionalBlocks :: Expression -> [Block] -> String -> TypecheckerState ()
typeCheckCondtionalBlocks exp bs errorMsg = do 
    curStore <- S.get 
    if not (checker curStore exp BooleanType) 
        then return $ Left errorMsg
        else return $ typeCheckBlocks curStore bs

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
    curRtName <- getReturnTypeName
    eExpectedType <- synth (Name curRtName)
    eActualType <- synthesis exp 
    env <- S.get
    return $ case (eExpectedType, eActualType) of 
        (Left l, _) -> Left l 
        (_, Left l) -> Left l
        (Right expectedType, Right actualType) -> if actualType <: expectedType 
            then Right () 
            else Left (errorMsg "Return" expectedType actualType ++ show env)

typeCheckAssign :: Var -> LType -> Expression -> TypecheckerState ()
typeCheckAssign v UnknownType exp = return $ Left ("Can not determine type of [" ++ pretty exp ++ "]")
typeCheckAssign v t exp = do 
    res <- doTypeAssignment v t exp-- Try to do type assignment, then evaluate expression type. (Recursive definitions)
    eTExpType <- synthesis exp 
    case eTExpType of 
        Left l -> return $ Left l
        Right tExpType -> if not (tExpType <: t) 
            then return $ Left (errorMsg "AssignmentError" t tExpType)
            else return $ Right () 
    
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

-- TODO: generalize two cases here. 
synthParams :: LType -> [Expression] -> TypecheckerState LType 
synthParams (FunctionType Never returnType) [] = return $ Right returnType
synthParams (FunctionType paramType returnType) [p] = do 
    ePType <- synthesis p
    case ePType of 
        l@(Left _) -> return l
        Right pType -> if pType <: paramType
                            then synthParams (FunctionType Never returnType) []
                            else return $ Left (errorMsg "ParameterAssignment" paramType pType)
synthParams (FunctionType paramType returnType) (p : ps) = do 
    ePType <- synthesis p
    env <- S.get
    case ePType of 
        l@(Left _) -> return l
        Right pType -> if pType <: paramType
                            then synthParams returnType ps
                            else return $ Left (errorMsg "ParameterAssignment" paramType pType ++ show env)
synthParams t _ = return $ Left (errorMsg "CallNonFunc" t (FunctionType Never AnyType))

-- TODO: generalize two cases. 
synthOp2 :: Bop -> Expression -> Expression -> TypecheckerState LType                            
synthOp2 op e1 e2 | isPolymorphicBop op = do 
    curStore <- S.get
    eSameType <- checkSameType e1 e2 
    case eSameType of 
        Right False -> return $ Left "Recieved two different types in Op2 execution."
        (Left error) -> return $ Left error
        Right True -> do 
            eOpType <- synth op 
            case eOpType of 
                Right opType -> synthParams opType [e1, e2]
                (Left error) -> return $ Left error
synthOp2 op e1 e2 = do 
            eOpType <- synth op 
            case eOpType of 
                Right opType -> synthParams opType [e1, e2]
                (Left error) -> return $ Left error

typeCheckFuncBody :: Name -> TypecheckerState () 
typeCheckFuncBody n = do 
    s <- S.get 
    let funcValue = getFuncFromEnv s n 
    case funcValue of 
        Just (FunctionVal pms rt b) -> do 
            prepareFunctionEnv pms rt
            S.modify (`removeFuncFromEnv` n)
            res <- typeCheckBlock b
            return $ Right ()
        _ -> return $ Left ("Failed to find function [" ++ n ++ "] in store") -- This should never happen. TODO: force it to be impossible.

synthesis :: Expression -> TypecheckerState LType  
synthesis (Call (Name n) pms) = do 
    typeCheckFuncBody n 
    eFType <- synthesis (Var (Name n))
    case eFType of 
        Right fType -> do 
            res <- synthParams fType pms 
            S.modify exitScope  
            return res
        l@(Left _) -> return l
synthesis (Op1 uop exp) = do 
    eOpType <- synth uop
    case eOpType of 
        Right opType -> synthParams opType [exp]
        l@(Left _) -> return l
synthesis (Op2 exp1 bop exp2) = synthOp2 bop exp1 exp2
synthesis (Val v) = synth v
synthesis (Var v) = synth v
synthesis (TableConst tfs) = synth tfs  

runSynthesis :: Environment -> Expression -> LType 
runSynthesis env exp = case S.evalState (synthesis exp) env of 
    Right t -> t 
    Left _ -> UnknownType

-- | Check that type of given expression is an instance of given type. 
checker :: Environment -> Expression -> LType -> Bool
checker env e = (<:) (runSynthesis env e)

