module Context where 

import Data.Map (Map)
import Data.Map qualified as Map
import Stack (Stack)
import Stack qualified
import LuTypes 
import LuSyntax 
import State (State)
import qualified State as S

class Environment env where 
    getContext :: env -> Context
    setContext :: env -> Context -> env 

    emptyEnv :: env 

    addGlobal :: (Name, LType) -> env -> env 
    addGlobal (k, v) env = let c = getContext env in setContext env $ c {gMap = Map.insert k v (gMap c)}

    addLocal :: (Name, LType) -> env -> env
    addLocal (k, v) env = let c = getContext env in setContext env $ c {localStack = Stack.push (localStack c) lv} where 
        lv = LocalVar {lType = v, name = k, depth = curDepth (getContext env)}
    
    getGlobal :: env -> Name -> Maybe LType 
    getGlobal env n = let c = getContext env in Map.lookup n (gMap c)

    getLocal :: env -> Name -> Maybe LType 
    getLocal env n = let c = getContext env in case Stack.peekUntil (localStack c) (\lv -> name lv == n) of 
        Just lv -> Just $ lType lv 
        _ -> Nothing

    get :: env -> Name -> Maybe LType 
    get env n = case (getGlobal env n, getLocal env n) of 
        (_, Just t) -> Just t
        (Just t, _) -> Just t 
        _ -> Nothing

    lookup :: Name -> State env (Maybe LType) 
    lookup n = S.get >>= \env -> return $ get env n

    -- | Decrease depth of scope and remove variables at this level. 
    exitScope :: env -> env
    exitScope env = let c = getContext env in setContext env $ c {localStack = Stack.popUntil (localStack c) (aboveDepth (curDepth c)), curDepth = curDepth c - 1} where 
        aboveDepth :: Int -> LocalVar a -> Bool 
        aboveDepth n lv = depth lv < curDepth (getContext env)

    -- | Increase depth of scope. 
    enterScope :: env -> env 
    enterScope env = let c = getContext env in setContext env $ c {curDepth = curDepth c + 1}

    setGMap :: env -> Map Name LType -> env 
    setGMap env m = let c = getContext env in setContext env $ c {gMap = m}


data Context = Context {
    gMap :: Map Name LType, 
    localStack :: Stack (LocalVar LType),  
    curDepth :: Int
}

instance Environment Context where 
    getContext = id 
    setContext _ = id 
    emptyEnv = Context {gMap = Map.empty, localStack = Stack.empty, curDepth = 0}

data LocalVar a = LocalVar {
    lType :: a,
    name :: Name,
    depth :: Int
}

instance Show a => Show (LocalVar a) where 
    show :: LocalVar a -> String 
    show lv = show (name lv) ++ "=" ++ show (lType lv) ++ ":" ++ show (depth lv)

instance Show Context where 
    show :: Context -> String 
    show env = show (gMap env) ++ "\n" ++ show (localStack env) ++ "\n" ++ "[depth=" ++ show (curDepth env) ++ "]"
    