module Context where

import Data.Map (Map)
import Data.Map qualified as Map
import LuSyntax
import LuTypes
import Stack (Stack)
import Stack qualified
import State (State)
import State qualified as S

data Context a = Context
  { gMap :: Map Value a,
    localStack :: Stack (LocalVar a),
    curDepth :: Int
  }

data Reference
  = GlobalRef Name -- name of global
  | LocalRef Name -- name of local
  | TableRef Name Value -- name of table, value that keys it.
  deriving (Eq, Show)

data LocalVar a = LocalVar
  { val :: a,
    name :: Name,
    depth :: Int
  }

class ExtendedContext ce where
  emptyContext :: ce
  exitScope :: ce -> ce
  enterScope :: ce -> ce

class (Eq v) => Environment a v where
  getContext :: a -> Context v
  setContext :: a -> Context v -> a

  index :: Reference -> State a v

  indexTable :: (Name, Value) -> v -> State a v

  updateTable :: (Name, Value) -> v -> State a ()

  lookup :: Name -> State a v

  indexWithDefault :: Reference -> v -> State a v
  indexWithDefault (GlobalRef n) d = do
    env <- S.get
    return $ case getGlobal n env of
      Just v -> v
      _ -> d
  indexWithDefault (LocalRef n) d = do
    env <- S.get
    return $ case getLocal n env of
      Just v -> v
      _ -> d
  indexWithDefault (TableRef tname tkey) d = indexTable (tname, tkey) d

  update :: Reference -> v -> State a ()
  update (GlobalRef n) v = S.modify (addGlobal (n, v))
  update (LocalRef n) v = S.modify (addLocal (n, v))
  update (TableRef n k) v = updateTable (n, k) v

  addLocal :: (Name, v) -> a -> a
  addLocal (n, v) env =
    let c = getContext env
     in let lv = LocalVar {val = v, name = n, depth = curDepth c}
         in setContext env (c {localStack = Stack.push (localStack c) lv})

  addGlobal :: (Name, v) -> a -> a
  addGlobal (k, v) env =
    let c = getContext env
     in setContext env (c {gMap = Map.insert (StringVal k) v (gMap c)})

  setGMap :: Map Value v -> a -> a
  setGMap m env =
    let c = getContext env
     in setContext env (c {gMap = m})

  getGlobal :: Name -> a -> Maybe v
  getGlobal n env = Map.lookup (StringVal n) ((gMap . getContext) env)

  getLocal :: Name -> a -> Maybe v
  getLocal n env = case Stack.peekUntil ((localStack . getContext) env) (\lv -> name lv == n) of
    Just lv -> Just $ val lv
    _ -> Nothing

  lookupWithUnknown :: v -> Name -> State a v
  lookupWithUnknown unknown n = do
    localResolve <- index (LocalRef n)
    globalResolve <- index (GlobalRef n)
    if localResolve == unknown
      then return globalResolve
      else return localResolve

  prepareFunctionEnv :: [(Name, v)] -> State a ()
  prepareFunctionEnv params = do
    let getThisContext = getContext :: a -> Context v
    S.modify (\env -> setContext env (enterScope (getThisContext env)))
    S.modify (\e -> foldr addLocal e params)

instance ExtendedContext (Context a) where
  emptyContext :: Context a
  emptyContext = Context {gMap = Map.empty, localStack = Stack.empty, curDepth = 0}

  -- \| Decrease depth of scope and remove variables at this level.
  exitScope :: Context a -> Context a
  exitScope c = c {localStack = Stack.popUntil (localStack c) (aboveDepth (curDepth c)), curDepth = curDepth c - 1}
    where
      aboveDepth :: Int -> LocalVar a -> Bool
      aboveDepth n lv = depth lv < curDepth c

  -- \| Increase depth of scope.
  enterScope :: Context a -> Context a
  enterScope c = c {curDepth = curDepth c + 1}

instance (Show a) => Show (LocalVar a) where
  show :: LocalVar a -> String
  show lv = show (name lv) ++ "=" ++ show (val lv) ++ ":" ++ show (depth lv)

instance (Show a) => Show (Context a) where
  show :: Context a -> String
  show env = show (gMap env) ++ "\n" ++ show (localStack env) ++ "\n" ++ "[depth=" ++ show (curDepth env) ++ "]"