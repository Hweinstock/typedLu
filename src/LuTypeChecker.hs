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

type EnvironmentTypes = Map Name LType
-- type TypecheckerState = EitherT (State EnvironmentTypes) ()  -- transformer version

type TypecheckerState = State EnvironmentTypes (Either String ())

returnTypeName :: Name 
returnTypeName = "@R"

typeCheckAST :: Block -> Either String () 
typeCheckAST b = S.evalState (typeCheckBlock b) Map.empty

getTypeEnv :: Block -> EnvironmentTypes 
getTypeEnv b = S.execState (typeCheckBlock b) Map.empty

-- | typeCheck blocks individually, with some state. 
typeCheckBlocks :: EnvironmentTypes -> [Block] -> Either String ()
typeCheckBlocks env = foldr checkBlock (Right ()) where 
    checkBlock :: Block -> Either String () -> Either String () 
    checkBlock b l@(Left _) = l 
    checkBlock b _ = S.evalState (typeCheckBlock b) env
    
-- | Check that given expression is boolean, then check underlying blocks.
typeCheckCondtionalBlocks :: Expression -> [Block] -> String -> TypecheckerState
typeCheckCondtionalBlocks exp bs errorMsg = do 
    curStore <- S.get 
    if not (checker curStore exp BooleanType) 
        then return $ Left errorMsg
        else return $ typeCheckBlocks curStore bs

-- | Given a block and an environment, check if the types are consistent in the block. 
typeCheckBlock :: Block -> TypecheckerState
typeCheckBlock (Block (s : ss)) = do 
    curCheck <- typeCheckStatement s 
    case curCheck of 
        l@(Left _) -> return l 
        Right () -> typeCheckBlock (Block ss)
typeCheckBlock (Block []) = return $ Right ()

-- | Given a statement and an environment, check if the types are consistent in the statement. 
typeCheckStatement :: Statement -> TypecheckerState
typeCheckStatement (Assign (v, t) exp) = typeCheckAssign v t exp
typeCheckStatement (If exp b1 b2) = typeCheckCondtionalBlocks exp [b1, b2] "Non-boolean in if condition"
typeCheckStatement (While exp b) = typeCheckCondtionalBlocks exp [b] "Non-boolean in while condition"
typeCheckStatement Empty = return $ Right ()  
typeCheckStatement (Repeat b exp) = typeCheckCondtionalBlocks exp [b] "Non-boolean in repeat condition"
typeCheckStatement (Return exp) = do 
    s <- S.get
    let expectedType = getTypeFromEnv s (Name "@R") 
    let actualType = synthesis s exp 
    if actualType <: expectedType 
        then return $ Right () 
        else return $ Left "Invalid return type"

typeCheckAssign :: Var -> LType -> Expression -> TypecheckerState
typeCheckAssign v UnknownType exp = do 
    s <- S.get 
    let tExp = synthesis s exp
    typeCheckAssign v tExp exp
typeCheckAssign v Never exp = return $ Left "Can't assign to never type."
typeCheckAssign v f@(FunctionType _ _) exp = do 
    s <- S.get 
    let oldReturnType = getTypeFromEnv s (Name "@R")
    let newReturnType = getFuncRType f 
    S.modify (Map.insert "@R" newReturnType)
    s2 <- S.get
    let tExpType = synthesis s2 exp 
    if not (tExpType <: f)
        then return $ Left ("TypeAssignmentError: Cannot assign [" ++ pretty tExpType ++ "] to [" ++ pretty f ++ "].")
    else do
        result <- doTypeAssignment s2 v f
        S.modify (Map.insert "@R" oldReturnType)
        return result

typeCheckAssign v t exp = do 
    s <- S.get 
    let tExpType = synthesis s exp 
    if not (tExpType <: t) then 
        return $ Left "Invalid type assignment"
    else doTypeAssignment s v t 
    
doTypeAssignment :: EnvironmentTypes -> Var -> LType -> TypecheckerState
doTypeAssignment s (Name n) tExpType = do 
    case getTypeFromEnv s (Name n) of 
        NilType -> updateTypeEnv n tExpType
        Never -> return $ Left "Unable to determine type of expression in assignment"
        realT -> if realT /= tExpType then 
            return $ Left "Cannot redefine variable to new type"
            else updateTypeEnv n tExpType
doTypeAssignment s (Dot tExp n) vExpType = 
    let tExpType = synthesis s tExp in
        return $ typecheckTableAccess (synthesis s tExp) StringType vExpType
doTypeAssignment s (Proj tExp kExp) vExpType = do 
    let kExpType = synthesis s kExp
        tExpType = synthesis s tExp in
            return $ typecheckTableAccess tExpType kExpType vExpType

typecheckTableAccess :: LType -> LType -> LType -> Either String ()
typecheckTableAccess (TableType kType vType) givenKType givenVType = 
    if givenKType <: kType && givenVType <: vType 
        then Right () 
        else Left "Table type sealed"
typecheckTableAccess _ _ _= Left "Unable to access value from non-table"

-- | Update variable type in store. 
updateTypeEnv :: Name -> LType -> TypecheckerState
updateTypeEnv n t = do 
    env <- S.get
    S.modify (Map.insert n t)
    return $ Right ()

isFunctionType :: LType -> Bool 
isFunctionType (FunctionType _ _ ) = True 
isFunctionType _ = False

-- | Lookup type in store, if not found, return NilType.
--   For dot/proj, if table doesn't exist -> Never, or if key type doesn't match type key type.
getTypeFromEnv :: EnvironmentTypes -> Var -> LType
getTypeFromEnv env (Name n) = case Map.lookup n env of 
    Just t -> t 
    _ -> NilType
getTypeFromEnv env (Dot exp n) = case synthesis env exp of 
    TableType t1 t2 -> if StringType <: t1 
        then t2 
        else Never
    _ -> Never 
getTypeFromEnv env (Proj exp1 exp2) = case (synthesis env exp1, synthesis env exp2) of 
    (TableType t1 t2, projType) -> if projType <: t1
        then t2 
        else Never
    _ -> Never
    

-- | IsSubtype: Return true if first type is valid subtype of the second. 
(<:) :: LType -> LType -> Bool 
(<:) a b | a == b = True
(<:) a Never = False
(<:) a AnyType = True 
(<:) (UnionType a1 a2) b = a1 <: b && a2 <: b
(<:) a (UnionType t1 t2) = a <: t1 || a <: t2
(<:) (TableType t1 t2) (TableType t3 t4) =  t1 <: t3 && t2 <: t4
(<:) (FunctionType t1 t2) (FunctionType t3 t4) = t3 <: t1 && t2 <: t4
(<:) _ _ = False

checkSameType :: EnvironmentTypes -> Expression -> Expression -> Bool 
checkSameType env e1 e2 = synthesis env e1 == synthesis env e2

getFuncRType :: LType -> LType 
getFuncRType (FunctionType _ f@(FunctionType _ _)) = getFuncRType f
getFuncRType (FunctionType _ r) = r 
getFuncRType _ = Never -- Should never hit this case. 

getFuncParamTypes :: LType -> [LType]
getFuncParamTypes (FunctionType t f@(FunctionType _ _ )) = t : getFuncParamTypes f 
getFuncParamTypes (FunctionType NilType _) = []
getFuncParamTypes (FunctionType t _) = [t]
getFuncParamTypes _ = [] -- Should never hit this case. 

synthTable :: EnvironmentTypes -> [TableField] -> LType
synthTable env tfs = let (keyTypes, valTypes) = unzip (map (synthTableField env) tfs) in 
    TableType (constructType keyTypes) (constructType valTypes) where 
        constructType :: [LType] -> LType 
        constructType = foldr constructTypeHelper UnknownType where 
            constructTypeHelper :: LType -> LType -> LType 
            constructTypeHelper t1 UnknownType = t1
            constructTypeHelper t1 accT | t1 <: accT = accT 
            constructTypeHelper t1 accT | accT <: t1 = t1 
            constructTypeHelper t1 accT = UnionType t1 accT

synthTableField :: EnvironmentTypes -> TableField -> (LType, LType)
synthTableField env (FieldName n e) = synthTableField env (FieldKey (Val (StringVal n)) e) -- If fieldName, treat it as a string indexer.
synthTableField env (FieldKey e1 e2) = (synthesis env e1, synthesis env e2) 

synthCall :: EnvironmentTypes -> Var -> [Expression] -> LType
synthCall env v = synthParams env (synthesis env (Var v))

-- | Generalized function to typecheck parameters for any function type. 
synthParams :: EnvironmentTypes -> LType -> [Expression] -> LType 
synthParams env (FunctionType NilType returnType) [] = returnType
synthParams env (FunctionType paramType (FunctionType _ _)) [p] = Never -- Not enough arguments
synthParams env (FunctionType paramType returnType) [p] = 
    if checker env p paramType then returnType else Never
synthParams env (FunctionType paramType returnType) (p : ps) = 
    if checker env p paramType then synthParams env returnType ps else Never
synthParams env _ _ = Never -- Shouldn't happen

synthVal :: EnvironmentTypes -> Value -> LType 
synthVal env NilVal = NilType
synthVal env (IntVal _) = IntType
synthVal env (BoolVal _) = BooleanType 
synthVal env (StringVal _) = StringType 
synthVal env (TableVal n) = undefined --what is this case? 
synthVal env (FunctionVal pms rt b) = case S.evalState (typeCheckBlock b) env of 
    Right () -> synthFunc pms rt
    Left _ -> Never
    where 
        synthFunc :: [Parameter] -> LType -> LType 
        synthFunc [] rt = FunctionType NilType rt 
        synthFunc [(_, t)] rt = FunctionType t rt
        synthFunc ((_, t) : ps) rt = FunctionType t (synthFunc ps rt)

synthOp1 :: EnvironmentTypes -> Uop -> Expression -> LType
synthOp1 env Neg e = let eIsInt = checker env e IntType in 
    if eIsInt then IntType else Never
synthOp1 env Not e = BooleanType 
synthOp1 env Len e = let eType = synthesis env e in 
    if isValidLenType eType then IntType else Never where 
        isValidLenType :: LType -> Bool 
        isValidLenType StringType = True 
        isValidLenType IntType = True 
        isValidLenType (TableType _ _) = True 
        isValidLenType _ = False 

arithmeticOpType :: LType
arithmeticOpType = FunctionType IntType (FunctionType IntType IntType)

comparisonOpType :: LType 
comparisonOpType = FunctionType AnyType (FunctionType AnyType BooleanType)

concatType :: LType 
concatType = FunctionType StringType (FunctionType StringType StringType)

synthOp2 :: EnvironmentTypes -> Bop -> Expression -> Expression -> LType                            
synthOp2 env Plus e1 e2 = synthParams env arithmeticOpType [e1, e2]
synthOp2 env Minus e1 e2 = synthParams env arithmeticOpType [e1, e2]
synthOp2 env Times e1 e2 = synthParams env arithmeticOpType [e1, e2]
synthOp2 env Divide e1 e2= synthParams env arithmeticOpType [e1, e2]
synthOp2 env Modulo e1 e2 = synthParams env arithmeticOpType [e1, e2]
synthOp2 env Eq e1 e2 = synthComparisonOp env e1 e2 
synthOp2 env Gt e1 e2 = synthComparisonOp env e1 e2  
synthOp2 env Ge e1 e2 = synthComparisonOp env e1 e2 
synthOp2 env Lt e1 e2 = synthComparisonOp env e1 e2 
synthOp2 env Le e1 e2 = synthComparisonOp env e1 e2 
synthOp2 env Concat e1 e2 = synthParams env concatType [e1, e2]

synthComparisonOp :: EnvironmentTypes -> Expression -> Expression -> LType
synthComparisonOp env e1 e2 = if checkSameType env e1 e2
    then synthParams env comparisonOpType [e1, e2]
    else Never -- not same type, can't compare

-- | Determine type of a given expression with environment. 
synthesis :: EnvironmentTypes -> Expression -> LType
synthesis env (Var v) = getTypeFromEnv env v
synthesis env (Val v) = synthVal env v
synthesis env (Op1 uop exp) = synthOp1 env uop exp
synthesis env (Op2 exp1 bop exp2) = synthOp2 env bop exp1 exp2
synthesis env (TableConst tfs) = synthTable env tfs  
synthesis env (Call v pms) = synthCall env v pms 

-- | Check that type of given expression is an instance of given type. 
checker :: EnvironmentTypes -> Expression -> LType -> Bool
checker env e = (<:) (synthesis env e)

