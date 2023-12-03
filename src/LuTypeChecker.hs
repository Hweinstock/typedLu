module LuTypeChecker where

import Control.Monad
import LuSyntax
import State (State)
import Data.Map (Map)
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

-- | Determine type of a given expression with environment. 
synthesis :: Expression -> EnvironmentTypes -> LType
synthesis = undefined

-- | Check that type of given expression is same as given type. 
checker :: Expression -> LType -> EnvironmentTypes -> Bool
checker = undefined