module LuTypes where

import Control.Applicative (liftA2)
import Test.QuickCheck (Arbitrary (..), Gen)
import qualified Test.QuickCheck as QC



-- Potentially add Unknown, Any as we see fit. 
data LType = 
    Never 
    | UnknownType
    | NilType
    | IntType
    | StringType
    | BooleanType
    | TableType LType LType -- What about a table as a key??
    | UnionType LType LType 
    | FunctionType LType LType -- Partial Function 
    deriving (Eq, Show)

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