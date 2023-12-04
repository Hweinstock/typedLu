module LuTypeChecker where

import Control.Monad
import LuSyntax
import State (State)
import Data.Map (Map)
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

getFunctionReturnType :: LType -> LType 
getFunctionReturnType (FunctionType _ f@(FunctionType _ _)) = getFunctionReturnType f
getFunctionReturnType (FunctionType _ r) = r 
getFunctionReturnType (FunctionType _ r) = Never

-- | Determine type of a given expression with environment. 
synthesis :: EnvironmentTypes -> Expression -> LType
synthesis env (Var v) = getTypeFromEnv env v
synthesis env (Val v) = synthVal v
synthesis env (Op1 uop exp) = synthOp1 env uop exp
synthesis env (Op2 exp1 bop exp2) = synthOp2 env bop exp1 exp2
synthesis env (TableConst tfs) = undefined 
synthesis env (Call v pms) = getFunctionReturnType $ synthesis env (Var v)

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

synthOp2 :: EnvironmentTypes -> Bop -> Expression -> Expression -> LType 
synthOp2 env Plus = synthBopType env IntType IntType
synthOp2 env Minus = synthBopType env IntType IntType
synthOp2 env Times = synthBopType env IntType IntType
synthOp2 env Divide = synthBopType env IntType IntType
synthOp2 env Modulo = synthBopType env IntType IntType
synthOp2 env Eq = synthBopType env AnyType BooleanType
synthOp2 env Gt = synthBopType env AnyType BooleanType 
synthOp2 env Ge = synthBopType env AnyType BooleanType 
synthOp2 env Lt = synthBopType env AnyType BooleanType 
synthOp2 env Le = synthBopType env AnyType BooleanType 
synthOp2 env Concat = synthBopType env StringType StringType

synthBopType :: EnvironmentTypes -> LType -> LType -> Expression -> Expression -> LType
synthBopType env targetT returnT e1 e2 = 
    if (checker env e1 targetT,  checker env e2 targetT) == (True, True) 
        then returnT 
        else Never 

-- | Check that type of given expression is same as given type. 
checker :: EnvironmentTypes -> Expression -> LType -> Bool
checker env (Var v) = undefined
checker env (Val v) = undefined 
checker env (Op1 uop exp) = undefined 
checker env (Op2 exp1 bop exp2) = undefined
checker env (TableConst tfs) = undefined 
checker env (Call v pms) = undefined 