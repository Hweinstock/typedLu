{-# LANGUAGE FunctionalDependencies #-}

module Context where

import Control.Monad.State (MonadState)
import Control.Monad.State qualified as State
import Data.Map (Map)
import Data.Map qualified as Map
import LuSyntax (Name, Value (StringVal))
import LuTypes
import Stack (Stack)
import Stack qualified

-- Shared Context between evaluator and type-checker.
data Context a = Context
  { gMap :: Map Value a,
    localStack :: Stack (LocalVar a),
    curDepth :: Int
  }

emptyContext :: Context a
emptyContext = Context {gMap = Map.empty, localStack = Stack.empty, curDepth = 0}

data Reference
  = GlobalRef Name -- name of global
  | LocalRef Name -- name of local
  | TableRef Name Value -- name of table, value that keys it.
  deriving (Eq, Show, Ord)

data LocalVar a = LocalVar
  { val :: a,
    name :: Name,
    depth :: Int
  }

-- | Define an environment type class that we can implement in TC + Eval.
-- We can define all the shared functionality of working with the environment here.
class (Eq v) => Environment env v | env -> v where
  emptyEnv :: env
  getContext :: env -> Context v
  setContext :: env -> Context v -> env

  index :: (MonadState env m) => Reference -> m v
  indexTable :: (MonadState env m) => (Name, Value) -> v -> m v
  updateTable :: (MonadState env m) => (Name, Value) -> v -> m ()
  resolveName :: (MonadState env m) => Name -> m (Reference, v)

  exitScope :: env -> env
  exitScope env =
    let c = getContext env
     in setContext env (exitContextScope c)
    where
      exitContextScope c = c {localStack = Stack.popUntil (localStack c) (aboveDepth (curDepth c)), curDepth = curDepth c - 1}
        where
          aboveDepth :: Int -> LocalVar a -> Bool
          aboveDepth n lv = depth lv < curDepth (getContext env)

  enterScope :: env -> env
  enterScope env =
    let c = getContext env
     in setContext env (c {curDepth = curDepth c + 1})

  indexWithDefault :: (MonadState env m) => Reference -> v -> m v
  indexWithDefault (GlobalRef n) d = do
    env <- State.get
    return $ case getGlobal n env of
      Just v -> v
      _ -> d
  indexWithDefault (LocalRef n) d = do
    env <- State.get
    return $ case getLocal n env of
      Just v -> v
      _ -> d
  indexWithDefault (TableRef tname tkey) d = indexTable (tname, tkey) d
  
  update :: (MonadState env m) => Reference -> v -> m ()
  update (GlobalRef n) v = State.modify (addGlobal (n, v) :: env -> env)
  update (LocalRef n) v = State.modify (addLocal (n, v))
  update (TableRef n k) v = updateTable (n, k) v

  -- Internal method.
  addLocal :: (Name, v) -> env -> env
  addLocal (n, v) env =
    let c = getContext env
     in let lv = LocalVar {val = v, name = n, depth = curDepth c}
         in setContext env (c {localStack = Stack.push (localStack c) lv})

  -- Internal method.
  addGlobal :: (Name, v) -> env -> env
  addGlobal (k, v) env =
    let c = getContext env
     in setContext env (c {gMap = Map.insert (StringVal k) v (gMap c)})


  getGlobal :: Name -> env -> Maybe v
  getGlobal n env = Map.lookup (StringVal n) ((gMap . getContext) env)

  getLocal :: Name -> env -> Maybe v
  getLocal n env = case Stack.peekUntil ((localStack . getContext) env) (\lv -> name lv == n) of
    Just lv -> Just $ val lv
    _ -> Nothing

  -- Set global map, useful for testing and initialization.
  setGMap :: Map Value v -> env -> env
  setGMap m env =
    let c = getContext env
     in setContext env (c {gMap = m})
     
  resolveNameWithUnknown :: (MonadState env m) => v -> Name -> m (Reference, v)
  resolveNameWithUnknown unknown n = do
    localResolve <- index (LocalRef n)
    globalResolve <- index (GlobalRef n)
    if localResolve == unknown
      then return (GlobalRef n, globalResolve)
      else return (LocalRef n, localResolve)

  prepareFunctionEnv :: (MonadState env m) => [(Name, v)] -> m ()
  prepareFunctionEnv params = do
    let getThisContext = getContext :: env -> Context v
    State.modify enterScope
    State.modify (\e -> foldr addLocal e params)

instance (Show a) => Show (LocalVar a) where
  show :: LocalVar a -> String
  show lv = show (name lv) ++ "=" ++ show (val lv) ++ ":" ++ show (depth lv)

instance (Show a) => Show (Context a) where
  show :: Context a -> String
  show env = show (gMap env) ++ "\n" ++ show (localStack env) ++ "\n" ++ "[depth=" ++ show (curDepth env) ++ "]"