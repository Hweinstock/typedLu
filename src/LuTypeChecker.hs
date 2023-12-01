module LuTypeChecker where

import LuSyntax
import State (State)
import Data.Map (Map)
import LuTypes 


isValueType :: LType -> Bool 
isValueType = undefined

type EnvironmentTypes = Map Name LType
type EnvironmentState = State EnvironmentTypes ()

-- | Given a block and an environment, check if the types are consistent in the block. 
typeCheckBlock :: Block -> EnvironmentState -> State EnvironmentTypes ()
typeCheckBlock = undefined

-- | Given a statement and an environment, check if the types are consistent in the statement. 
typeCheckStatement :: Statement -> EnvironmentState -> State EnvironmentTypes () 
typeCheckStatement = undefined

-- | Determine type of a given expression and with environment. 
synthesis :: Expression -> EnvironmentTypes -> LType
synthesis = undefined

-- | Check that type of given expression is same as given type. 
checker :: Expression -> LType -> EnvironmentTypes -> Bool
checker = undefined