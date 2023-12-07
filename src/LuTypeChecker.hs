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
type SynthesisState = State EnvironmentTypes LType

class Synthable a where
    synth :: EnvironmentTypes -> a -> LType 

instance Synthable Uop where 
    synth _ Neg = FunctionType IntType IntType
    synth _ Not = FunctionType AnyType BooleanType 
    synth _ Len = FunctionType (UnionType IntType (UnionType StringType (TableType AnyType AnyType))) IntType  

instance Synthable Bop where 
    synth _ Plus = FunctionType IntType (FunctionType IntType IntType)
    synth _ Minus = FunctionType IntType (FunctionType IntType IntType)
    synth _ Times = FunctionType IntType (FunctionType IntType IntType)
    synth _ Divide = FunctionType IntType (FunctionType IntType IntType)
    synth _ Modulo = FunctionType IntType (FunctionType IntType IntType)
    synth _ Eq = FunctionType AnyType (FunctionType AnyType BooleanType)
    synth _ Gt = FunctionType AnyType (FunctionType AnyType BooleanType)
    synth _ Ge = FunctionType AnyType (FunctionType AnyType BooleanType)
    synth _ Lt = FunctionType AnyType (FunctionType AnyType BooleanType)
    synth _ Le = FunctionType AnyType (FunctionType AnyType BooleanType)
    synth _ Concat = FunctionType StringType (FunctionType StringType StringType)

instance Synthable Value where 
    synth env NilVal = NilType
    synth env (IntVal _) = IntType
    synth env (BoolVal _) = BooleanType 
    synth env (StringVal _) = StringType 
    synth env (TableVal n) = undefined --what is this case? 
    synth env (FunctionVal pms rt b) = 
        let functionEnv = prepareFunctionEnv pms rt in 
            case S.evalState (typeCheckBlock b) functionEnv of 
        Right () -> synthFunc pms rt
        Left _ -> UnknownType
        where 
            synthFunc :: [Parameter] -> LType -> LType 
            synthFunc [] rt = FunctionType NilType rt 
            synthFunc [(_, t)] rt = FunctionType t rt
            synthFunc ((_, t) : ps) rt = FunctionType t (synthFunc ps rt)
            prepareFunctionEnv :: [Parameter] -> LType -> EnvironmentTypes 
            prepareFunctionEnv pms rt = foldr addToEnv env (("@R", rt) : pms) where 
                addToEnv :: (Name, LType) -> EnvironmentTypes -> EnvironmentTypes
                addToEnv (k, v) = Map.insert k v

instance Synthable [TableField] where 
    synth env tfs = let (keyTypes, valTypes) = unzip (map (synthTableField env) tfs) in 
        TableType (constructType keyTypes) (constructType valTypes) 
        where 
            synthTableField :: EnvironmentTypes -> TableField -> (LType, LType)
            synthTableField env (FieldName n e) = synthTableField env (FieldKey (Val (StringVal n)) e) -- If fieldName, treat it as a string indexer.
            synthTableField env (FieldKey e1 e2) = (synthesis env e1, synthesis env e2) 

            constructType :: [LType] -> LType 
            constructType = foldr constructTypeHelper UnknownType where 
                constructTypeHelper :: LType -> LType -> LType 
                constructTypeHelper t1 UnknownType = t1
                constructTypeHelper t1 accT | t1 <: accT = accT 
                constructTypeHelper t1 accT | accT <: t1 = t1 
                constructTypeHelper t1 accT = UnionType t1 accT

-- | Lookup type in store, if not found, return NilType.
--   For dot/proj, if table doesn't exist -> Unknown, or if key type doesn't match expected key type.
instance Synthable Var where 
    synth env (Name n) = case Map.lookup n env of 
        Just t -> t 
        _ -> NilType
    synth env (Dot exp n) = let tExp = synthesis env exp in 
        case (typecheckTableAccess tExp StringType Never, tExp) of 
            (Right (), TableType t1 t2) -> t2 
            _ -> UnknownType 
    synth env (Proj tExp kExp) = 
        let tableType = synthesis env tExp
            keyType = synthesis env kExp 
        in case (typecheckTableAccess tableType keyType Never, tableType) of 
            (Right (), TableType t1 t2) -> t2 
            _ -> UnknownType

isPolymorphicBop :: Bop -> Bool
isPolymorphicBop Eq = True 
isPolymorphicBop Gt = True 
isPolymorphicBop Ge = True 
isPolymorphicBop Lt = True 
isPolymorphicBop Le = True 
isPolymorphicBop _ = False 

returnTypeName :: Name 
returnTypeName = "@R"

typeCheckAST :: Block -> Either String () 
typeCheckAST b = S.evalState (typeCheckBlock b) Map.empty

getTypeEnv :: Block -> Either String EnvironmentTypes 
getTypeEnv b = case S.runState (typeCheckBlock b) Map.empty of 
    (Right (), finalStore) -> Right finalStore
    (Left l, finalStore) -> Left l
    
-- | Generate error message with a type, expected type, and actual type. 
errorMsg :: String -> LType -> LType -> String 
errorMsg errorType expectedType actualType = 
    errorType ++ ": expected type [" ++ pretty expectedType ++ "] got type [" ++ pretty actualType ++ "]" 

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
typeCheckStatement (Assign (v, UnknownType) exp) = S.get >>= \s -> typeCheckAssign v (synthesis s exp) exp
typeCheckStatement (Assign (v, t) exp) = typeCheckAssign v t exp
typeCheckStatement (If exp b1 b2) = typeCheckCondtionalBlocks exp [b1, b2] "Non-boolean in if condition"
typeCheckStatement (While exp b) = typeCheckCondtionalBlocks exp [b] "Non-boolean in while condition"
typeCheckStatement Empty = return $ Right ()  
typeCheckStatement (Repeat b exp) = typeCheckCondtionalBlocks exp [b] "Non-boolean in repeat condition"
typeCheckStatement (Return exp) = do 
    s <- S.get
    let expectedType = synth s (Name "@R") 
    let actualType = synthesis s exp 
    if actualType <: expectedType 
        then return $ Right () 
        else return $ Left (errorMsg "Return" expectedType actualType)

typeCheckAssign :: Var -> LType -> Expression -> TypecheckerState
typeCheckAssign v UnknownType exp = return $ Left ("Can not determine type of [" ++ pretty exp ++ "]")
typeCheckAssign v t exp = do 
    s <- S.get 
    res <- doTypeAssignment s v t -- Try to do type assignment, then evaluate expression type. (Recursive definitions)
    s2 <- S.get
    let tExpType = synthesis s2 exp 
    if not (tExpType <: t) then 
        --doTypeAssignment s v UnknownType -- Undo type assignment if it fails
        return $ Left (errorMsg "AssignmentError" t tExpType)
    else doTypeAssignment s v t 
    
doTypeAssignment :: EnvironmentTypes -> Var -> LType -> TypecheckerState
doTypeAssignment s (Name n) tExpType = do 
    case synth s (Name n) of 
        NilType -> updateTypeEnv n tExpType
        UnknownType -> return $ Left "Unable to determine type of expression in assignment"
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

-- | IsSubtype: Return true if first type is valid subtype of the second. 
(<:) :: LType -> LType -> Bool 
(<:) a b | a == b = True
(<:) a UnknownType = True 
(<:) UnknownType b = False
(<:) Never b = True
(<:) a Never = False
(<:) a AnyType = True 
(<:) (UnionType a1 a2) b = a1 <: b && a2 <: b
(<:) a (UnionType t1 t2) = a <: t1 || a <: t2
(<:) (TableType t1 t2) (TableType t3 t4) =  t1 <: t3 && t2 <: t4
(<:) (FunctionType t1 t2) (FunctionType t3 t4) = t3 <: t1 && t2 <: t4
(<:) _ _ = False

checkSameType :: EnvironmentTypes -> Expression -> Expression -> Bool 
checkSameType env e1 e2 = t1 <: t2 && t2 <: t1 where 
    t1 = synthesis env e1
    t2 = synthesis env e2

getFuncRType :: LType -> LType 
getFuncRType (FunctionType _ f@(FunctionType _ _)) = getFuncRType f
getFuncRType (FunctionType _ r) = r 
getFuncRType _ = UnknownType -- Should never hit this case. 

getFuncParamTypes :: LType -> [LType]
getFuncParamTypes (FunctionType t f@(FunctionType _ _ )) = t : getFuncParamTypes f 
getFuncParamTypes (FunctionType NilType _) = []
getFuncParamTypes (FunctionType t _) = [t]
getFuncParamTypes _ = [] -- Should never hit this case. 

synthCall :: EnvironmentTypes -> Var -> [Expression] -> LType
synthCall env v = synthParams env (synthesis env (Var v))

-- | Generalized function to typecheck parameters for any function type. 
synthParams :: EnvironmentTypes -> LType -> [Expression] -> LType 
synthParams env (FunctionType NilType returnType) [] = returnType
synthParams env (FunctionType paramType (FunctionType _ _)) [p] = UnknownType -- Not enough arguments
synthParams env (FunctionType paramType returnType) [p] = 
    if checker env p paramType then returnType else UnknownType
synthParams env (FunctionType paramType returnType) (p : ps) = 
    if checker env p paramType then synthParams env returnType ps else UnknownType
synthParams env _ _ = UnknownType -- Shouldn't happen

synthOp2 :: EnvironmentTypes -> Bop -> Expression -> Expression -> LType                            
synthOp2 env op e1 e2 | isPolymorphicBop op = if checkSameType env e1 e2 
    then synthParams env (synth env op) [e1, e2]
    else UnknownType -- not same type, can't compare
synthOp2 env op e1 e2 = synthParams env (synth env op) [e1, e2]

-- | Determine type of a given expression with environment. 
synthesis :: EnvironmentTypes -> Expression -> LType
synthesis env (Op1 uop exp) = synthParams env (synth env uop) [exp]
synthesis env (Op2 exp1 bop exp2) = synthOp2 env bop exp1 exp2
synthesis env (Call v pms) = synthCall env v pms 
synthesis env (Val v) = synth env v
synthesis env (Var v) = synth env v
synthesis env (TableConst tfs) = synth env tfs  

synthesisWithState :: Expression -> SynthesisState 
synthesisWithState exp = do
    s <- S.get 
    return $ synthesis s exp 

-- | Check that type of given expression is an instance of given type. 
checker :: EnvironmentTypes -> Expression -> LType -> Bool
checker env e = (<:) (synthesis env e)

