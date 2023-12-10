module Context where 

import Data.Map (Map)
import Data.Map qualified as Map
import Stack (Stack)
import Stack qualified
import LuTypes 
import LuSyntax 
import State (State)
import qualified State as S



data Context a = Context {
    gMap :: Map Value a, 
    localStack :: Stack (LocalVar a),  
    curDepth :: Int
}

data Reference = 
    GlobalRef Name -- name of global
  | LocalRef Name  -- name of local
  | TableRef Name Value  -- name of table, value that keys it. 
  deriving (Eq, Show)

data LocalVar a = LocalVar {
    val :: a,
    name :: Name,
    depth :: Int
}

class Environment a v where 
    getContext :: a -> Context v 
    setContext :: a -> Context v -> a 

    index :: Reference -> State a v 

    update :: Reference -> v -> State a ()
    update (GlobalRef n) v = S.modify (addGlobal (n, v)) 
    update (LocalRef n) v = S.modify (addLocal (n, v))
    update (TableRef n k) v = updateTable (n, k) v 

    updateTable :: (Name, Value) -> v -> State a () 

    addLocal :: (Name, v) -> a -> a 
    addLocal (n, v) env = let c = getContext env in
                          let lv = LocalVar {val = v, name = n, depth = curDepth c} in 
        setContext env (c {localStack = Stack.push (localStack c) lv}) 
    
    addGlobal :: (Name, v) -> a -> a 
    addGlobal (k, v) env = let c = getContext env in
        setContext env (c {gMap = Map.insert (StringVal k) v (gMap c)})

    setGMap :: Map Value v -> a -> a 
    setGMap m env = let c = getContext env in 
        setContext env (c {gMap = m})

    getGlobal :: Name -> a -> Maybe v 
    getGlobal n env = Map.lookup (StringVal n) ((gMap . getContext) env)

    getLocal :: Name -> a -> Maybe v 
    getLocal n env = case Stack.peekUntil ((localStack . getContext) env) (\lv -> name lv == n) of 
        Just lv -> Just $ val lv 
        _ -> Nothing

-- | Decrease depth of scope and remove variables at this level. 
exitScope :: Context a -> Context a
exitScope c = c {localStack = Stack.popUntil (localStack c) (aboveDepth (curDepth c)), curDepth = curDepth c - 1} where 
    aboveDepth :: Int -> LocalVar a -> Bool 
    aboveDepth n lv = depth lv < curDepth c

-- | Increase depth of scope. 
enterScope :: Context a -> Context a
enterScope c = c {curDepth = curDepth c + 1}

-- setGMap :: Context a -> Map Value a -> Context a
-- setGMap c m = c {gMap = m}

emptyContext :: Context a 
emptyContext = Context {gMap = Map.empty, localStack = Stack.empty, curDepth = 0}

instance Show a => Show (LocalVar a) where 
    show :: LocalVar a -> String 
    show lv = show (name lv) ++ "=" ++ show (val lv) ++ ":" ++ show (depth lv)

instance Show a => Show (Context a) where 
    show :: Context a -> String 
    show env = show (gMap env) ++ "\n" ++ show (localStack env) ++ "\n" ++ "[depth=" ++ show (curDepth env) ++ "]"
    