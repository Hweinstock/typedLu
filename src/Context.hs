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
    gMap :: Map Name a, 
    localStack :: Stack (LocalVar a),  
    curDepth :: Int
}

data LocalVar a = LocalVar {
    val :: a,
    name :: Name,
    depth :: Int
}

addGlobal :: (Name, a) -> Context a -> Context a
addGlobal (k, v) c = c {gMap = Map.insert k v (gMap c)}

addLocal :: (Name, a) -> Context a -> Context a 
addLocal (k, v) c = c {localStack = Stack.push (localStack c) lv} where 
    lv = LocalVar {val = v, name = k, depth = curDepth c}

getGlobal :: Context a -> Name -> Maybe a 
getGlobal c n = Map.lookup n (gMap c)

getLocal :: Context a -> Name -> Maybe a 
getLocal c n = case Stack.peekUntil (localStack c) (\lv -> name lv == n) of 
    Just lv -> Just $ lType lv 
    _ -> Nothing

get :: Context a -> Name -> Maybe a 
get c n = case (getGlobal c n, getLocal c n) of 
    (_, Just t) -> Just t
    (Just t, _) -> Just t 
    _ -> Nothing
    
-- | Decrease depth of scope and remove variables at this level. 
exitScope :: Context a -> Context a
exitScope c = c {localStack = Stack.popUntil (localStack c) (aboveDepth (curDepth c)), curDepth = curDepth c - 1} where 
    aboveDepth :: Int -> LocalVar a -> Bool 
    aboveDepth n lv = depth lv < curDepth c

-- | Increase depth of scope. 
enterScope :: Context a -> Context a
enterScope c = c {curDepth = curDepth c + 1}

setGMap :: Context a -> Map Name a -> Context a
setGMap c m = c {gMap = m}

emptyContext :: Context a 
emptyContext = Context {gMap = Map.empty, localStack = Stack.empty, curDepth = 0}

instance Show a => Show (LocalVar a) where 
    show :: LocalVar a -> String 
    show lv = show (name lv) ++ "=" ++ show (lType lv) ++ ":" ++ show (depth lv)

instance Show a => Show (Context a) where 
    show :: Context a -> String 
    show env = show (gMap env) ++ "\n" ++ show (localStack env) ++ "\n" ++ "[depth=" ++ show (curDepth env) ++ "]"
    