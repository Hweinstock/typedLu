module LuTypeChecker where

import Control.Monad
import LuSyntax
import State (State)
import qualified State as S
import Data.Map (Map)
import Data.List (nub)
import qualified Data.Map as Map
import LuTypes 

newtype EitherT m a = EitherT { runEitherT :: m (Either String a) }

instance Monad m => Monad (EitherT m) where 
    return :: a -> EitherT m a
    return = pure 
    (>>=) = bind where 
        bind :: EitherT m a -> (a -> EitherT m b) -> EitherT m b
        bind x f = EitherT $ do 
            eitherValue <- runEitherT x 
            case eitherValue of 
                Left s -> return $ Left s
                Right v -> runEitherT $ f v

instance Monad m => Applicative (EitherT m) where
    pure = EitherT . return . Right
    (<*>) = ap

instance Monad m => Functor (EitherT m) where
    fmap = liftM

data Environment = Environment {
    typeMap :: Map Name LType,
    functionMap :: Map Name Value
}

addTypeToEnv :: (Name, LType) -> Environment -> Environment
addTypeToEnv (k, v) env = env {typeMap = Map.insert k v (typeMap env)}

addFuncToEnv :: (Name, Value) -> Environment -> Environment
addFuncToEnv (k, v) env = env {functionMap = Map.insert k v (functionMap env)}

getTypeFromEnv :: Environment -> Name -> Maybe LType 
getTypeFromEnv env n = Map.lookup n (typeMap env)

getFuncFromEnv :: Environment -> Name -> Maybe Value 
getFuncFromEnv env n = Map.lookup n (functionMap env)

removeFuncFromEnv :: Environment -> Name -> Environment 
removeFuncFromEnv env n = env {functionMap = Map.delete n (functionMap env)}

-- type TypecheckerState = EitherT (State EnvironmentTypes) ()  -- transformer version

type TypecheckerState a = State Environment (Either String a)

class Synthable2 a where 
    synth2 :: a -> TypecheckerState LType

instance Synthable2 Uop where 
    synth2 Neg = return $ return $ FunctionType IntType IntType
    synth2 Not = return $ return $ FunctionType AnyType BooleanType 
    synth2 Len = return $ return $ FunctionType (UnionType IntType (UnionType StringType (TableType AnyType AnyType))) IntType  

instance Synthable2 Bop where 
    synth2 Plus = return $ return $ FunctionType IntType (FunctionType IntType IntType)
    synth2 Minus = return $ return $ FunctionType IntType (FunctionType IntType IntType)
    synth2 Times = return $ return $ FunctionType IntType (FunctionType IntType IntType)
    synth2 Divide = return $ return $ FunctionType IntType (FunctionType IntType IntType)
    synth2 Modulo = return $ return $ FunctionType IntType (FunctionType IntType IntType)
    synth2 Eq = return $ return $ FunctionType AnyType (FunctionType AnyType BooleanType)
    synth2 Gt = return $ return $ FunctionType AnyType (FunctionType AnyType BooleanType)
    synth2 Ge = return $ return $ FunctionType AnyType (FunctionType AnyType BooleanType)
    synth2 Lt = return $ return $ FunctionType AnyType (FunctionType AnyType BooleanType)
    synth2 Le = return $ return $ FunctionType AnyType (FunctionType AnyType BooleanType)
    synth2 Concat = return $ return $ FunctionType StringType (FunctionType StringType StringType)

instance Synthable2 Value where 
    synth2 NilVal = return $ return NilType
    synth2 (IntVal _) = return $ return IntType
    synth2 (BoolVal _) = return $ return BooleanType 
    synth2 (StringVal _) = return $ return StringType 
    synth2 (TableVal n) = undefined --what is this case? 
    synth2 (FunctionVal pms rt b) = do 
        prepareFunctionEnv2 pms rt 
        env <- S.get
        return $ case S.evalState (typeCheckBlock b) env of 
            Right () -> Right $ synthFunc pms rt
            Left l -> Left l
            where 
                synthFunc :: [Parameter] -> LType -> LType 
                synthFunc [] rt = FunctionType Never rt 
                synthFunc [(_, t)] rt = FunctionType t rt
                synthFunc ((_, t) : ps) rt = FunctionType t (synthFunc ps rt)

instance Synthable2 Var where 
    synth2 (Name n) = do 
        s <- S.get 
        case getTypeFromEnv s n of 
            Just t -> return $ Right t 
            _ -> return $ Right NilType
    synth2 (Dot exp n) = do 
        eTExp <- synthesisWithState exp 
        return $ case eTExp of 
            Left l -> Left l 
            Right tExp@(TableType t1 t2) -> case typecheckTableAccess tExp StringType Never of 
                Right () -> Right t2 
                Left l -> Left l
            Right _ -> Left "Cannot access not table type via dot method."

    synth2 (Proj tExp kExp) = do 
        eTableType <- synthesisWithState tExp 
        eKeyType <- synthesisWithState kExp 

        return $ case (eTableType, eKeyType) of 
            (Left l, _) -> Left l 
            (_, Left l) -> Left l
            (Right tableType@(TableType t1 t2), Right keyType) -> case typecheckTableAccess tableType keyType Never of 
                Right () -> Right t2 
                Left l -> Left l
            _ -> Left "Cannot access not table type via proj method."

instance Synthable2 [TableField] where 
    synth2 tfs = do 
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
            eT1 <- synthesisWithState e1 
            eT2 <- synthesisWithState e2 
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
class Synthable a where
    synth :: Environment -> a -> LType 

instance Synthable Uop where 
    synth _ Neg = FunctionType IntType IntType
    synth _ Not = FunctionType AnyType BooleanType 
    synth _ Len = FunctionType (UnionType IntType (UnionType StringType (TableType AnyType AnyType))) IntType  

instance Synthable Bop where 
    synth _ Plus = FunctionType IntType (FunctionType IntType IntType)
    synth _ Minus = FunctionType IntType (FunctionType IntType IntType)
    synth _ Times = FunctionType IntType (FunctionType IntType IntType)
    synth _ Divide = FunctionType IntType (FunctionType IntType IntType)
    synth _ Modulo = FunctionType IntType (FunctionType IntType IntType)
    synth _ Eq = FunctionType AnyType (FunctionType AnyType BooleanType)
    synth _ Gt = FunctionType AnyType (FunctionType AnyType BooleanType)
    synth _ Ge = FunctionType AnyType (FunctionType AnyType BooleanType)
    synth _ Lt = FunctionType AnyType (FunctionType AnyType BooleanType)
    synth _ Le = FunctionType AnyType (FunctionType AnyType BooleanType)
    synth _ Concat = FunctionType StringType (FunctionType StringType StringType)

instance Synthable Value where 
    synth env NilVal = NilType
    synth env (IntVal _) = IntType
    synth env (BoolVal _) = BooleanType 
    synth env (StringVal _) = StringType 
    synth env (TableVal n) = undefined --what is this case? 
    synth env (FunctionVal pms rt b) = 
        let functionEnv = prepareFunctionEnv env pms rt in 
            case S.evalState (typeCheckBlock b) functionEnv of 
                Right () -> synthFunc pms rt
                Left _ -> UnknownType
                where 
                    synthFunc :: [Parameter] -> LType -> LType 
                    synthFunc [] rt = FunctionType Never rt 
                    synthFunc [(_, t)] rt = FunctionType t rt
                    synthFunc ((_, t) : ps) rt = FunctionType t (synthFunc ps rt)

-- | Return new environment with initialized parameters and return flag in given environment. 
prepareFunctionEnv :: Environment -> [Parameter] -> LType -> Environment 
prepareFunctionEnv env pms rt = foldr addTypeToEnv env (("@R", rt) : pms) 

prepareFunctionEnv2 :: [Parameter] -> LType -> State Environment ()
prepareFunctionEnv2 pms rt = S.modify (\e -> foldr addTypeToEnv e (("@R", rt) : pms))

instance Synthable [TableField] where 
    synth env tfs = let (keyTypes, valTypes) = unzip (map (synthTableField env) tfs) in 
        TableType (constructType keyTypes) (constructType valTypes) 
        where 
            synthTableField :: Environment -> TableField -> (LType, LType)
            synthTableField env (FieldName n e) = synthTableField env (FieldKey (Val (StringVal n)) e) -- If fieldName, treat it as a string indexer.
            synthTableField env (FieldKey e1 e2) = (synthesis env e1, synthesis env e2) 

            constructType :: [LType] -> LType 
            constructType = foldr constructTypeHelper UnknownType where 
                constructTypeHelper :: LType -> LType -> LType 
                constructTypeHelper t1 UnknownType = t1
                constructTypeHelper t1 accT | t1 <: accT = accT 
                constructTypeHelper t1 accT | accT <: t1 = t1 
                constructTypeHelper t1 accT = UnionType t1 accT

-- | Lookup type in store, if not found, return NilType.
--   For dot/proj, if table doesn't exist -> Unknown, or if key type doesn't match expected key type.
instance Synthable Var where 
    synth env (Name n) = case Map.lookup n (typeMap env) of 
        Just t -> t 
        _ -> NilType
    synth env (Dot exp n) = let tExp = synthesis env exp in 
        case (typecheckTableAccess tExp StringType Never, tExp) of 
            (Right (), TableType t1 t2) -> t2 
            _ -> UnknownType 
    synth env (Proj tExp kExp) = 
        let tableType = synthesis env tExp
            keyType = synthesis env kExp 
        in case (typecheckTableAccess tableType keyType Never, tableType) of 
            (Right (), TableType t1 t2) -> t2 
            _ -> UnknownType

isPolymorphicBop :: Bop -> Bool
isPolymorphicBop Eq = True 
isPolymorphicBop Gt = True 
isPolymorphicBop Ge = True 
isPolymorphicBop Lt = True 
isPolymorphicBop Le = True 
isPolymorphicBop _ = False 

returnTypeName :: Name 
returnTypeName = "@R"

emptyStore :: Environment 
emptyStore = Environment {typeMap = Map.empty, functionMap = Map.empty}

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
    eTexp <- synthesisWithState exp 
    case eTexp of 
        Right t -> typeCheckAssign v t exp 
        Left l -> return $ Left l 
typeCheckStatement (Assign (v, t) exp) = typeCheckAssign v t exp
typeCheckStatement (If exp b1 b2) = typeCheckCondtionalBlocks exp [b1, b2] "Non-boolean in if condition"
typeCheckStatement (While exp b) = typeCheckCondtionalBlocks exp [b] "Non-boolean in while condition"
typeCheckStatement Empty = return $ Right ()  
typeCheckStatement (Repeat b exp) = typeCheckCondtionalBlocks exp [b] "Non-boolean in repeat condition"
typeCheckStatement (Return exp) = do 
    eExpectedType <- synth2 (Name "@R")
    eActualType <- synthesisWithState exp 
    return $ case (eExpectedType, eActualType) of 
        (Left l, _) -> Left l 
        (_, Left l) -> Left l
        (Right expectedType, Right actualType) -> if actualType <: expectedType 
            then Right () 
            else Left (errorMsg "Return" expectedType actualType)

typeCheckAssign :: Var -> LType -> Expression -> TypecheckerState ()
typeCheckAssign v UnknownType exp = return $ Left ("Can not determine type of [" ++ pretty exp ++ "]")
typeCheckAssign v t exp = do 
    res <- doTypeAssignment v t exp-- Try to do type assignment, then evaluate expression type. (Recursive definitions)
    eTExpType <- synthesisWithState exp 
    case eTExpType of 
        Left l -> return $ Left l
        Right tExpType -> if not (tExpType <: t) 
            then return $ Left (errorMsg "AssignmentError" t tExpType)
            else doTypeAssignment v t exp
    
doTypeAssignment ::  Var -> LType -> Expression -> TypecheckerState ()
doTypeAssignment (Name n) tExpType exp = do 
    etv <- synth2 (Name n)
    case etv of 
        Left l -> return $ Left l
        Right NilType -> updateEnv n tExpType exp
        Right UnknownType -> return $ Left "Unable to determine type of expression in assignment"
        Right realT -> if realT /= tExpType then 
            return $ Left "Cannot redefine variable to new type"
            else updateEnv n tExpType exp
doTypeAssignment (Dot tExp n) vExpType _ = do 
    eTExpType <- synthesisWithState tExp 
    return $ case eTExpType of 
        Left l -> Left l 
        Right tExpType -> typecheckTableAccess tExpType StringType vExpType
doTypeAssignment (Proj tExp kExp) vExpType _ = do 
    eKExpType <- synthesisWithState kExp
    eTExpType <- synthesisWithState tExp
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
    S.modify (addTypeToEnv (n, t))
    case (t, exp) of 
        (FunctionType _ _, Val f) -> do 
            S.modify (addFuncToEnv (n, f))
            return $ Right () 
        _ -> return $ Right ()

-- | IsSubtype: Return true if first type is valid subtype of the second. 
(<:) :: LType -> LType -> Bool 
(<:) a b | a == b = True
(<:) a UnknownType = True 
(<:) UnknownType b = False
(<:) Never b = True
(<:) a Never = False
(<:) a AnyType = True 
(<:) (UnionType a1 a2) b = a1 <: b && a2 <: b
(<:) a (UnionType t1 t2) = a <: t1 || a <: t2
(<:) (TableType t1 t2) (TableType t3 t4) =  t1 <: t3 && t2 <: t4
(<:) (FunctionType t1 t2) (FunctionType t3 t4) = t3 <: t1 && t2 <: t4
(<:) _ _ = False

checkSameTypeWithState :: Expression -> Expression -> TypecheckerState Bool 
checkSameTypeWithState e1 e2 = do 
    eT1 <- synthesisWithState e1 
    eT2 <- synthesisWithState e2
    case (eT1, eT2) of 
        (Right t1, Right t2) -> return $ Right (t1 <: t2 && t2 <: t1)
        (Left error, _) -> return $ Left error
        (_, Left error) -> return $ Left error

checkSameType :: Environment -> Expression -> Expression -> Bool 
checkSameType env e1 e2 = t1 <: t2 && t2 <: t1 where 
    t1 = synthesis env e1
    t2 = synthesis env e2

-- | Generalized function to typecheck parameters for any function type. 
synthParams :: Environment -> LType -> [Expression] -> LType 
synthParams env (FunctionType Never returnType) [] = returnType
synthParams env (FunctionType paramType returnType) [p] = 
    if checker env p paramType then returnType else UnknownType
synthParams env (FunctionType paramType returnType) (p : ps) = 
    if checker env p paramType then synthParams env returnType ps else UnknownType
synthParams env _ _ = UnknownType -- Attempt to call non-function type. 

-- TODO: generalize two cases here. 
synthParamsWithState :: LType -> [Expression] -> TypecheckerState LType 
synthParamsWithState (FunctionType Never returnType) [] = return $ Right returnType
synthParamsWithState (FunctionType paramType returnType) [p] = do 
    ePType <- synthesisWithState p
    case ePType of 
        l@(Left _) -> return l
        Right pType -> if pType <: paramType
                            then synthParamsWithState (FunctionType Never returnType) []
                            else return $ Left (errorMsg "ParameterAssignment" paramType pType)
synthParamsWithState (FunctionType paramType returnType) (p : ps) = do 
    ePType <- synthesisWithState p
    case ePType of 
        l@(Left _) -> return l
        Right pType -> if pType <: paramType
                            then synthParamsWithState returnType ps
                            else return $ Left (errorMsg "ParameterAssignment" paramType pType)
synthParamsWithState t _ = return $ Left (errorMsg "CallNonFunc" t (FunctionType Never AnyType))

synthOp2 :: Environment -> Bop -> Expression -> Expression -> LType                            
synthOp2 env op e1 e2 | isPolymorphicBop op = if checkSameType env e1 e2 
    then synthParams env (synth env op) [e1, e2]
    else UnknownType -- not same type, can't compare
synthOp2 env op e1 e2 = synthParams env (synth env op) [e1, e2]

-- TODO: generalize two cases. 
synthOp2WithState :: Bop -> Expression -> Expression -> TypecheckerState LType                            
synthOp2WithState op e1 e2 | isPolymorphicBop op = do 
    curStore <- S.get
    eSameType <- checkSameTypeWithState e1 e2 
    case eSameType of 
        Right False -> return $ Left "Recieved two different types in Op2 execution."
        (Left error) -> return $ Left error
        Right True -> do 
            eOpType <- synth2 op 
            case eOpType of 
                Right opType -> synthParamsWithState opType [e1, e2]
                (Left error) -> return $ Left error
synthOp2WithState op e1 e2 = do 
            eOpType <- synth2 op 
            case eOpType of 
                Right opType -> synthParamsWithState opType [e1, e2]
                (Left error) -> return $ Left error

-- | Determine type of a given expression with environment. 
synthesis :: Environment -> Expression -> LType
synthesis env (Op1 uop exp) = synthParams env (synth env uop) [exp]
synthesis env (Op2 exp1 bop exp2) = synthOp2 env bop exp1 exp2
synthesis env (Call v pms) = synthParams env (synthesis env (Var v)) pms
synthesis env (Val v) = synth env v
synthesis env (Var v) = synth env v
synthesis env (TableConst tfs) = synth env tfs  

typeCheckFuncBody :: Name -> TypecheckerState () 
typeCheckFuncBody n = do 
    s <- S.get 
    let funcValue = getFuncFromEnv s n 
    case funcValue of 
        Just (FunctionVal pms rt b) -> do 
            prepareFunctionEnv2 pms rt
            S.modify (\e -> removeFuncFromEnv e n)
            typeCheckBlock b
        _ -> return $ Left ("Failed to find function [" ++ n ++ "] in store") -- This should never happen. TODO: force it to be impossible.

synthesisWithState :: Expression -> TypecheckerState LType  
synthesisWithState (Call (Name n) pms) = do 
    typeCheckFuncBody n 
    eFType <- synthesisWithState (Var (Name n))
    case eFType of 
        Right fType -> synthParamsWithState fType pms 
        l@(Left _) -> return l
synthesisWithState (Op1 uop exp) = do 
    eOpType <- synth2 uop
    case eOpType of 
        Right opType -> synthParamsWithState opType [exp]
        l@(Left _) -> return l
synthesisWithState (Op2 exp1 bop exp2) = synthOp2WithState bop exp1 exp2
synthesisWithState (Val v) = synth2 v
synthesisWithState (Var v) = synth2 v
synthesisWithState (TableConst tfs) = synth2 tfs  

runSynthesis :: Environment -> Expression -> LType 
runSynthesis env exp = case S.evalState (synthesisWithState exp) env of 
    Right t -> t 
    Left _ -> UnknownType

-- | Check that type of given expression is an instance of given type. 
checker :: Environment -> Expression -> LType -> Bool
checker env e = (<:) (runSynthesis env e)

