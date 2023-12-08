module LuTypes where
import Test.QuickCheck (Arbitrary (..), Gen)



-- Potentially add Unknown, Any as we see fit. 
data LType = 
    Never 
    | AnyType
    | UnknownType
    | NilType
    | IntType
    | StringType
    | BooleanType
    | TableType LType LType -- What about a table as a key??
    | UnionType LType LType 
    | FunctionType LType LType -- Partial Function 
    deriving (Eq, Show)

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

instance Arbitrary LType where
    arbitrary :: Gen LType
    arbitrary = undefined

    shrink :: LType -> [LType]
    shrink = undefined
