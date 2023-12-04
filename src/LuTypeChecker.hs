module LuTypeChecker where

import Control.Monad
import LuSyntax
import State (State)
import Data.Map (Map)
import Data.List (nub)
import qualified Data.Map as Map
import LuTypes 


isValueType :: LType -> Bool 
isValueType = undefined

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

-- | Given a block and an environment, check if the types are consistent in the block. 
typeCheckBlock :: Block -> TypecheckerState
typeCheckBlock = undefined

-- | Given a statement and an environment, check if the types are consistent in the statement. 
typeCheckStatement :: Statement -> TypecheckerState
typeCheckStatement = undefined

getTypeFromEnv :: EnvironmentTypes -> Var -> LType
getTypeFromEnv env (Name n) = case Map.lookup n env of 
    Just t -> t 
    _ -> NilType

-- | Return true if the first type is an instance of the second type. 
isTypeInstanceOf :: LType -> LType -> Bool 
isTypeInstanceOf a b | a == b = True 
isTypeInstanceOf a AnyType = True 
isTypeInstanceOf (UnionType a1 a2) b = isTypeInstanceOf a1 b && isTypeInstanceOf a2 b
isTypeInstanceOf a (UnionType t1 t2) = isTypeInstanceOf a t1 || isTypeInstanceOf a t2
isTypeInstanceOf _ _ = False

getFunctionReturnType :: LType -> LType 
getFunctionReturnType (FunctionType _ f@(FunctionType _ _)) = getFunctionReturnType f
getFunctionReturnType (FunctionType _ r) = r 
getFunctionReturnType _ = Never -- Should never hit this case. 

getFunctionParameterTypes :: LType -> [LType]
getFunctionParameterTypes (FunctionType t f@(FunctionType _ _ )) = t : getFunctionParameterTypes f 
getFunctionParameterTypes (FunctionType NilType _) = []
getFunctionParameterTypes (FunctionType t _) = [t]
getFunctionParameterTypes _ = [] -- Should never hit this case. 

-- | Determine type of a given expression with environment. 
synthesis :: EnvironmentTypes -> Expression -> LType
synthesis env (Var v) = getTypeFromEnv env v
synthesis env (Val v) = synthVal v
synthesis env (Op1 uop exp) = synthOp1 env uop exp
synthesis env (Op2 exp1 bop exp2) = synthOp2 env bop exp1 exp2
synthesis env (TableConst tfs) = synthTable env tfs  
synthesis env (Call v pms) = synthCall env v pms 

synthTable :: EnvironmentTypes -> [TableField] -> LType
synthTable env tfs = let (keyTypes, valTypes) = unzip (map (synthTableField env) tfs) in 
    TableType (constructType keyTypes) (constructType valTypes) where 
        constructType :: [LType] -> LType 
        constructType [] = UnknownType
        constructType [t] = t 
        constructType (t : ts) | any (isTypeInstanceOf t) ts = constructType ts
        constructType [t1, t2] = UnionType t1 t2 
        constructType (t : ts) = UnionType t (constructType ts)

synthTableField :: EnvironmentTypes -> TableField -> (LType, LType)
synthTableField env (FieldName n e) = synthTableField env (FieldKey (Val (StringVal n)) e) -- If fieldName, treat it as a string indexer.
synthTableField env (FieldKey e1 e2) = (synthesis env e1, synthesis env e2) 


synthCall :: EnvironmentTypes -> Var -> [Expression] -> LType
synthCall env v = synthFunction env functionType where 
    functionType = synthesis env (Var v)

synthFunction :: EnvironmentTypes -> LType -> [Expression] -> LType 
synthFunction env functionType params = if checkParamTypes functionType paramTypes
    then getFunctionReturnType functionType 
    else Never 
        where 
            paramTypes = map (synthesis env) params

synthVar :: EnvironmentTypes -> Var -> LType
synthVar env nm@(Name n) = getTypeFromEnv env nm 
synthVar env (Dot exp n) = undefined 
synthVar env (Proj exp1 exp2) = undefined 

synthVal :: Value -> LType 
synthVal NilVal = NilType
synthVal (IntVal _) = IntType
synthVal (BoolVal _) = BooleanType 
synthVal (StringVal _) = StringType 
synthVal (TableVal n) = undefined --what is this case? 
synthVal (FunctionVal pms rt _) = synthFunc pms rt

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
synthOp2 env Plus e1 e2 = synthFunction env arithmeticOpType [e1, e2]
synthOp2 env Minus e1 e2 = synthFunction env arithmeticOpType [e1, e2]
synthOp2 env Times e1 e2 = synthFunction env arithmeticOpType [e1, e2]
synthOp2 env Divide e1 e2= synthFunction env arithmeticOpType [e1, e2]
synthOp2 env Modulo e1 e2 = synthFunction env arithmeticOpType [e1, e2]
synthOp2 env Eq e1 e2 = synthComparisonOp env e1 e2 
synthOp2 env Gt e1 e2 = synthComparisonOp env e1 e2  
synthOp2 env Ge e1 e2 = synthComparisonOp env e1 e2 
synthOp2 env Lt e1 e2 = synthComparisonOp env e1 e2 
synthOp2 env Le e1 e2 = synthComparisonOp env e1 e2 
synthOp2 env Concat e1 e2 = synthFunction env concatType [e1, e2]

synthComparisonOp :: EnvironmentTypes -> Expression -> Expression -> LType
synthComparisonOp env e1 e2 = if checkSameType env e1 e2
    then synthFunction env comparisonOpType [e1, e2]
    else Never -- not same type, can't compare

-- | Check that type of given expression is an instance of given type. 
checker :: EnvironmentTypes -> Expression -> LType -> Bool
checker env e@(Var v) t = isTypeInstanceOf (synthesis env e) t
checker env e@(Val v) t = isTypeInstanceOf (synthesis env e) t
checker env e@(Op1 uop exp) t = isTypeInstanceOf (synthesis env e) t
checker env e@(Op2 exp1 bop exp2) t = isTypeInstanceOf (synthesis env e) t
checker env e@(TableConst tfs) t = isTypeInstanceOf (synthesis env e) t  
checker env e@(Call v pms) t = isTypeInstanceOf (synthesis env e) t 

checkParamTypes :: LType -> [LType] -> Bool 
checkParamTypes functionType paramTypes = 
    let expectedPmsTypes = getFunctionParameterTypes functionType in 
    let zipTypes = zip expectedPmsTypes paramTypes in 
    let checkTypePair (expected, actual) = isTypeInstanceOf actual expected in
        all checkTypePair zipTypes && length expectedPmsTypes == length paramTypes

checkSameType :: EnvironmentTypes -> Expression -> Expression -> Bool 
checkSameType env e1 e2 = synthesis env e1 == synthesis env e2
