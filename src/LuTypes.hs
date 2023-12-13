module LuTypes where

import Control.Applicative (liftA2)
import Test.QuickCheck (Arbitrary (..), Gen)
import qualified Test.QuickCheck as QC



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
    deriving (Ord, Eq, Show)

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

constructUnionType :: [LType] -> LType 
constructUnionType = foldr constructTypeHelper UnknownType where 
    constructTypeHelper :: LType -> LType -> LType 
    constructTypeHelper t1 UnknownType = t1
    constructTypeHelper t1 accT | t1 <: accT = accT 
    constructTypeHelper t1 accT | accT <: t1 = t1 
    constructTypeHelper t1 accT = UnionType t1 accT

instance Arbitrary LType where
    arbitrary :: Gen LType
    arbitrary = let base = 3 in QC.frequency [
        (0, return Never), 
        (base, arbitraryBase), 
        (1, liftA2 TableType arbitrary arbitrary), 
        (1, liftA2 UnionType arbitraryBase arbitrary), 
        (1, liftA2 FunctionType arbitraryBase arbitrary)]
        where 
            arbitraryBase :: Gen LType 
            arbitraryBase = QC.elements [NilType, IntType, StringType, BooleanType]

    shrink :: LType -> [LType]
    shrink (TableType t1 t2) = [t1, t2]
    shrink (UnionType t1 t2) = [t1, t2]
    shrink (FunctionType t1 t2) = [t1, t2]
    shrink _ = []
