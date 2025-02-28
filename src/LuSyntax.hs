module LuSyntax where

import Control.Monad (mapM_)
import Control.Applicative (liftA2)
import qualified Data.Char as Char
import Data.Map (Map)
import LuTypes
import qualified Data.Map as Map
import Test.HUnit
import Test.QuickCheck (Arbitrary (..), Gen)
import qualified Test.QuickCheck as QC
import Text.PrettyPrint (Doc, (<+>))
import qualified Text.PrettyPrint as PP
import Data.Hashable (hash)
import qualified Data.Maybe

newtype Block = Block [Statement] -- s1 ... sn
  deriving (Eq, Show)

instance Semigroup Block where
  Block s1 <> Block s2 = Block (s1 <> s2)

instance Monoid Block where
  mempty = Block []

data Statement
  = Assign TypedVar Expression -- x = e or x: type = e
  | If Expression Block Block -- if e then s1 else s2 end
  | While Expression Block -- while e do s end
  | Empty -- ';'
  | Repeat Block Expression -- repeat s until e
  | Return Expression -- return e
  deriving (Eq, Show)

type TypedVar = (Var, LType)
type TypedExpression = (Expression, LType)

data Expression
  = Var Var -- global variables x and table indexing
  | Val Value -- literal values
  | Op1 Uop Expression -- unary operators
  | Op2 Expression Bop Expression -- binary operators
  | TableConst [TableField] -- table construction, { x = 3 , y = 5 }
  | Call Var [Expression] -- foo(x, y)
  deriving (Eq, Show)

data Value
  = NilVal -- nil
  | IntVal Int -- 1
  | BoolVal Bool -- false, true
  | StringVal String -- "abd"
  | TableVal Name -- <not used in source programs>
  | FunctionVal [Parameter] LType Block --function (v1: t1): t2
  | ErrorVal ErrorCode
  deriving (Eq, Show)

data ErrorCode = IllegalArguments | DivideByZero | UnknownError deriving (Eq, Show, Enum)

type Parameter = (Name, LType)

data Uop
  = Neg -- `-` :: Int -> Int
  | Not -- `not` :: a -> Bool
  | Len -- `#` :: String | Int | Table -> Int
  deriving (Eq, Show, Enum, Bounded)

data Bop
  = Plus -- `+`  :: Int -> Int -> Int
  | Minus -- `-`  :: Int -> Int -> Int
  | Times -- `*`  :: Int -> Int -> Int
  | Divide -- `//` :: Int -> Int -> Int   -- floor division
  | Modulo -- `%`  :: Int -> Int -> Int   -- modulo
  | Eq -- `==` :: a -> a -> Bool
  | Gt -- `>`  :: a -> a -> Bool
  | Ge -- `>=` :: a -> a -> Bool
  | Lt -- `<`  :: a -> a -> Bool
  | Le -- `<=` :: a -> a -> Bool
  | Concat -- `..` :: String -> String -> String
  deriving (Eq, Show, Enum, Bounded)

type Name = String -- either the name of a variable or the name of a field

data Var
  = Name Name -- x, global variable
  | Dot Expression Name -- t.x, access table using string key
  | Proj Expression Expression -- t[1], access table table using any type of key
  deriving (Eq, Show)

data TableField
  = FieldName Name Expression -- x = 3,
  | FieldKey Expression Expression -- ["x"] = true , [1] = 4 , [true] = "a"
  deriving (Eq, Show)

var :: String -> Expression
var = Var . Name

-- | Helper function to hash value data types. 
hashVal :: Value -> Int
hashVal NilVal = hash "NilVal"
hashVal (IntVal i) = hash i
hashVal (BoolVal b) = hash b
hashVal (StringVal s) = hash s
hashVal (TableVal n) = hash $ "table" ++ n
hashVal (FunctionVal ps rt b) = hash (show ps ++ show rt ++ show b)
hashVal (ErrorVal s) = hash $ fromEnum s

-- | Implement custom Ord via hasing since function values make deriving Ord difficult. 
instance Ord Value where
  v1 `compare` v2 = hashVal v1 `compare` hashVal v2

-- test.lu
wTest :: Block
wTest =
  Block
    [ Assign
        (Name "x", UnknownType)
        ( Op2
            ( Op2
                (Op2 (Val (IntVal 1)) Plus (Val (IntVal 2)))
                Minus
                (Val (IntVal 3))
            )
            Plus
            (Op2 (Val (IntVal 1)) Plus (Val (IntVal 3)))
        ),
      Assign (Name "y", UnknownType) (Val (IntVal 0)),
      While
        (Op2 (var "x") Gt (Val (IntVal 0)))
        ( Block
            [ Assign (Name "y", UnknownType) (Op2 (var "y") Plus (var "x")),
              Assign (Name "x", UnknownType) (Op2 (var "x") Minus (Val (IntVal 1)))
            ]
        )
    ]

-- fact.lu
wFact :: Block
wFact =
  Block
    [ Assign (Name "n", UnknownType) (Val (IntVal 5)),
      Assign (Name "f", UnknownType) (Val (IntVal 1)),
      While
        (Op2 (var "n") Gt (Val (IntVal 0)))
        ( Block
            [ Assign (Name "x", UnknownType) (Var (Name "n")),
              Assign (Name "z", UnknownType) (Var (Name "f")),
              While
                (Op2 (var "x") Gt (Val (IntVal 1)))
                ( Block
                    [ Assign (Name "f", UnknownType) (Op2 (var "z") Plus (Var (Name "f"))),
                      Assign (Name "x", UnknownType) (Op2 (var "x") Minus (Val (IntVal 1)))
                    ]
                ),
              Assign (Name "n", UnknownType) (Op2 (Var (Name "n")) Minus (Val (IntVal 1)))
            ]
        )
    ]

-- abs.lu
wAbs :: Block
wAbs =
  Block
    [ Assign (Name "x", UnknownType) (Op2 (Val (IntVal 0)) Minus (Val (IntVal 3))),
      If
        (Op2 (Var (Name "x")) Lt (Val (IntVal 0)))
        (Block [Assign (Name "x", UnknownType) (Op2 (Val (IntVal 0)) Minus (Var (Name "x")))])
        (Block [])
    ]

-- times.lu
wTimes :: Block
wTimes =
  Block
    [ Assign (Name "x", UnknownType) (Val (IntVal 10)),
      Assign (Name "y", UnknownType) (Val (IntVal 3)),
      Assign (Name "z", UnknownType) (Val (IntVal 0)),
      While
        (Op2 (Var (Name "x")) Gt (Val (IntVal 0)))
        ( Block
            [ Assign (Name "z", UnknownType) (Op2 (Var (Name "z")) Plus (Var (Name "y"))),
              Assign (Name "x", UnknownType) (Op2 (Var (Name "x")) Minus (Val (IntVal 1)))
            ]
        )
    ]

-- table.lu
wTable :: Block
wTable = Block [Assign (Name "a", UnknownType) (TableConst []), Assign (Name "k", UnknownType) (Val (StringVal "x")), Assign (Proj (Var (Name "a")) (Var (Name "k")), UnknownType) (Val (IntVal 10)), Assign (Proj (Var (Name "a")) (Val (IntVal 20)), UnknownType) (Val (StringVal "great")), Assign (Name "o1", UnknownType) (Var (Proj (Var (Name "a")) (Val (StringVal "x")))), Assign (Name "k", UnknownType) (Val (IntVal 20)), Assign (Name "o2", UnknownType) (Var (Proj (Var (Name "a")) (Var (Name "k")))), Assign (Proj (Var (Name "a")) (Val (StringVal "x")), UnknownType) (Op2 (Var (Proj (Var (Name "a")) (Val (StringVal "x")))) Plus (Val (IntVal 1))), Assign (Name "o3", UnknownType) (Var (Proj (Var (Name "a")) (Val (StringVal "x"))))]

-- bfs.lu
wBfs :: Block
wBfs = Block [Assign (Name "start", UnknownType) (Val (IntVal 1)), Assign (Name "goal", UnknownType) (Val (IntVal 10)), Empty, Assign (Name "graph", UnknownType) (TableConst []), Assign (Proj (Var (Name "graph")) (Val (IntVal 1)), UnknownType) (TableConst [FieldKey (Val (IntVal 1)) (Val (IntVal 2)), FieldKey (Val (IntVal 2)) (Val (IntVal 3))]), Assign (Proj (Var (Name "graph")) (Val (IntVal 2)), UnknownType) (TableConst [FieldKey (Val (IntVal 1)) (Val (IntVal 6)), FieldKey (Val (IntVal 2)) (Val (IntVal 5)), FieldKey (Val (IntVal 3)) (Val (IntVal 1))]), Assign (Proj (Var (Name "graph")) (Val (IntVal 3)), UnknownType) (TableConst [FieldKey (Val (IntVal 1)) (Val (IntVal 1))]), Assign (Proj (Var (Name "graph")) (Val (IntVal 4)), UnknownType) (TableConst [FieldKey (Val (IntVal 1)) (Val (IntVal 7)), FieldKey (Val (IntVal 2)) (Val (IntVal 8))]), Assign (Proj (Var (Name "graph")) (Val (IntVal 5)), UnknownType) (TableConst [FieldKey (Val (IntVal 1)) (Val (IntVal 9)), FieldKey (Val (IntVal 2)) (Val (IntVal 10)), FieldKey (Val (IntVal 3)) (Val (IntVal 2))]), Assign (Proj (Var (Name "graph")) (Val (IntVal 6)), UnknownType) (TableConst [FieldKey (Val (IntVal 1)) (Val (IntVal 2))]), Assign (Proj (Var (Name "graph")) (Val (IntVal 7)), UnknownType) (TableConst [FieldKey (Val (IntVal 1)) (Val (IntVal 4)), FieldKey (Val (IntVal 2)) (Val (IntVal 11)), FieldKey (Val (IntVal 3)) (Val (IntVal 12))]), Assign (Proj (Var (Name "graph")) (Val (IntVal 8)), UnknownType) (TableConst [FieldKey (Val (IntVal 1)) (Val (IntVal 4))]), Assign (Proj (Var (Name "graph")) (Val (IntVal 9)), UnknownType) (TableConst [FieldKey (Val (IntVal 1)) (Val (IntVal 5))]), Assign (Proj (Var (Name "graph")) (Val (IntVal 10)), UnknownType) (TableConst [FieldKey (Val (IntVal 1)) (Val (IntVal 5))]), Assign (Proj (Var (Name "graph")) (Val (IntVal 11)), UnknownType) (TableConst [FieldKey (Val (IntVal 1)) (Val (IntVal 7))]), Assign (Proj (Var (Name "graph")) (Val (IntVal 12)), UnknownType) (TableConst [FieldKey (Val (IntVal 1)) (Val (IntVal 7))]), Empty, Assign (Name "q", UnknownType) (TableConst [FieldName "elements" (TableConst []), FieldName "first" (Val (IntVal 0)), FieldName "last" (Val (IntVal 0))]), Assign (Proj (Var (Dot (Var (Name "q")) "elements")) (Var (Dot (Var (Name "q")) "last")), UnknownType) (Var (Name "start")), Assign (Dot (Var (Name "q")) "last", UnknownType) (Op2 (Var (Dot (Var (Name "q")) "last")) Plus (Val (IntVal 1))), Empty, Assign (Name "visited", UnknownType) (TableConst []), Assign (Proj (Var (Name "visited")) (Var (Name "start")), UnknownType) (Val (BoolVal True)), Assign (Name "found", UnknownType) (Val (BoolVal False)), Empty, Repeat (Block [Assign (Name "node", UnknownType) (Var (Proj (Var (Dot (Var (Name "q")) "elements")) (Var (Dot (Var (Name "q")) "first")))), Assign (Proj (Var (Dot (Var (Name "q")) "elements")) (Var (Dot (Var (Name "q")) "first")), UnknownType) (Val NilVal), Assign (Dot (Var (Name "q")) "first", UnknownType) (Op2 (Var (Dot (Var (Name "q")) "first")) Plus (Val (IntVal 1))), Empty, Assign (Proj (Var (Name "visited")) (Var (Name "node")), UnknownType) (Val (BoolVal True)), If (Op2 (Var (Name "goal")) Eq (Var (Name "node"))) (Block [Assign (Name "found", UnknownType) (Val (BoolVal True)), Assign (Dot (Var (Name "q")) "first", UnknownType) (Var (Dot (Var (Name "q")) "last"))]) (Block [Assign (Name "i", UnknownType) (Val (IntVal 1)), While (Op2 (Var (Name "i")) Le (Op1 Len (Var (Proj (Var (Name "graph")) (Var (Name "node")))))) (Block [Assign (Name "next", UnknownType) (Var (Proj (Var (Proj (Var (Name "graph")) (Var (Name "node")))) (Var (Name "i")))), If (Op1 Not (Var (Proj (Var (Name "visited")) (Var (Name "next"))))) (Block [Assign (Proj (Var (Dot (Var (Name "q")) "elements")) (Var (Dot (Var (Name "q")) "last")), UnknownType) (Var (Name "next")), Assign (Dot (Var (Name "q")) "last", UnknownType) (Op2 (Var (Dot (Var (Name "q")) "last")) Plus (Val (IntVal 1)))]) (Block [Empty]), Assign (Name "i", UnknownType) (Op2 (Var (Name "i")) Plus (Val (IntVal 1)))])])]) (Op2 (Op2 (Var (Dot (Var (Name "q")) "last")) Minus (Var (Dot (Var (Name "q")) "first"))) Eq (Val (IntVal 0)))]

-- >>> wTest
-- Block [Assign (Name "x") (Op2 (Op2 (Op2 (Val (IntVal 1)) Plus (Val (IntVal 2))) Minus (Val (IntVal 3))) Plus (Op2 (Val (IntVal 1)) Plus (Val (IntVal 3)))),Assign (Name "y") (Val (IntVal 0)),While (Op2 (Var (Name "x")) Gt (Val (IntVal 0))) (Block [Assign (Name "y") (Op2 (Var (Name "y")) Plus (Var (Name "x"))),Assign (Name "x") (Op2 (Var (Name "x")) Minus (Val (IntVal 1)))])]

-- >>> pretty wTest
-- "x = 1 + 2 - 3 + (1 + 3)\ny = 0\nwhile x > 0 do\n  y = y + x\n  x = x - 1\nend"

class PP a where
  pp :: a -> Doc

-- | Default operation for the pretty printer. Displays using standard formatting
-- rules, with generous use of indentation and newlines.
pretty :: PP a => a -> String
pretty = PP.render . pp

-- | Compact version. Displays its argument without newlines.
oneLine :: PP a => a -> String
oneLine = PP.renderStyle (PP.style {PP.mode = PP.OneLineMode}) . pp

instance PP Uop where
  pp Neg = PP.char '-'
  pp Not = PP.text "not"
  pp Len = PP.char '#'

instance PP Bool where
  pp True = PP.text "true"
  pp False = PP.text "false"

instance PP String where
  pp = PP.text

instance PP Int where
  pp = PP.int

instance PP TypedVar where
  pp (v, t) = pp v <> PP.char ':' <> pp t

instance PP LType where
  pp Never = PP.text "never"
  pp AnyType = PP.text "any"
  pp UnknownType = PP.text "unknown"
  pp NilType = PP.text "nil"
  pp IntType = PP.text "int"
  pp StringType = PP.text "string"
  pp BooleanType = PP.text "boolean"
  pp (TableType t1 t2) = PP.braces (pp t1 <> PP.char ':' <> pp t2)
  pp (UnionType t1 t2) = pp t1 <> PP.char '|' <> pp t2
  pp (FunctionType t1 t2) = pp t1 <> PP.text "->" <> pp t2

instance PP Var where
  pp (Name n) = PP.text n
  pp (Dot (Var v) k) = pp v <> PP.text "." <> pp k
  pp (Dot t k) = PP.parens (pp t) <> PP.text "." <> pp k
  pp (Proj (Var v) k) = pp v <> PP.brackets (pp k)
  pp (Proj t k) = PP.parens (pp t) <> PP.brackets (pp k)

instance PP Value where
  pp (IntVal i) = pp i
  pp (BoolVal b) = pp b
  pp NilVal = PP.text "nil"
  pp (StringVal s) = PP.text ("\"" <> s <> "\"")
  pp (TableVal t) = PP.text "<" <> PP.text t <> PP.text ">"
  pp (FunctionVal ps rt b) = PP.vcat [PP.text "function" <> PP.parens (ppParameters ps) <> PP.char ':' <> pp rt, pp b]
  pp (ErrorVal s) = undefined

instance PP Parameter where
  pp (n, t) = pp n <> PP.char ':' <> pp t

isBase :: Expression -> Bool
isBase TableConst {} = True
isBase Val {} = True
isBase Var {} = True
isBase Op1 {} = True
isBase _ = False

instance PP Bop where
  pp Plus = PP.char '+'
  pp Minus = PP.char '-'
  pp Times = PP.char '*'
  pp Divide = PP.text "//"
  pp Modulo = PP.text "%"
  pp Gt = PP.char '>'
  pp Ge = PP.text ">="
  pp Lt = PP.char '<'
  pp Le = PP.text "<="
  pp Eq = PP.text "=="
  pp Concat = PP.text ".."

instance PP Expression where
  pp (Var v) = pp v
  pp (Val v) = pp v
  pp (Op1 o v) = pp o <+> if isBase v then pp v else PP.parens (pp v)
  pp e@Op2 {} = ppPrec 0 e
    where
      ppPrec n (Op2 e1 bop e2) =
        ppParens (level bop < n) $
          ppPrec (level bop) e1 <+> pp bop <+> ppPrec (level bop + 1) e2
      ppPrec _ e' = pp e'
      ppParens b = if b then PP.parens else id
  pp (TableConst fs) = PP.braces (PP.sep (PP.punctuate PP.comma (map pp fs)))
  pp (Call fv ps) = pp fv <> PP.parens (PP.hsep (map pp ps))

instance PP TableField where
  pp (FieldName name e) = pp name <+> PP.equals <+> pp e
  pp (FieldKey e1 e2) = PP.brackets (pp e1) <+> PP.equals <+> pp e2

instance PP Block where
  pp (Block [s]) = pp s
  pp (Block ss) = PP.vcat (map pp ss)

ppSS :: [Statement] -> Doc
ppSS ss = PP.vcat (map pp ss)

ppParameters :: [Parameter] -> Doc
ppParameters ps = PP.hsep (map pp ps)

instance PP Statement where
  pp (Assign x e) = pp x <+> PP.equals <+> pp e
  pp (If guard b1 b2) =
    PP.hang (PP.text "if" <+> pp guard <+> PP.text "then") 2 (pp b1)
      PP.$$ PP.nest 2 (PP.text "else" PP.$$ pp b2)
      PP.$$ PP.text "end"
  pp (While guard e) =
    PP.hang (PP.text "while" <+> pp guard <+> PP.text "do") 2 (pp e)
      PP.$+$ PP.text "end"
  pp Empty = PP.semi
  pp (Repeat b e) =
    PP.hang (PP.text "repeat") 2 (pp b)
      PP.$+$ PP.text "until" <+> pp e
  pp (Return e) = PP.text "return" <+> pp e

level :: Bop -> Int
level Times = 7
level Divide = 7
level Plus = 5
level Minus = 5
level Concat = 4
level _ = 3 -- comparison operators

instance PP a => PP (Map Value a) where
  pp m = PP.braces (PP.vcat (map ppa (Map.toList m)))
    where
      ppa (StringVal s, v2) = PP.text s <+> PP.text "=" <+> pp v2
      ppa (v1, v2) = PP.brackets (pp v1) <+> PP.text "=" <+> pp v2

instance PP a => PP (Map Name a) where
  pp m = PP.braces (PP.vcat (map ppa (Map.toList m)))
    where
      ppa (s, v2) = PP.text s <+> PP.text "=" <+> pp v2

sampleVar :: IO ()
sampleVar = QC.sample' (arbitrary :: Gen Var) >>= mapM_ (print . pp)

sampleExp :: IO ()
sampleExp = QC.sample' (arbitrary :: Gen Expression) >>= mapM_ (print . pp)

sampleStat :: IO ()
sampleStat = QC.sample' (arbitrary :: Gen Statement) >>= mapM_ (print . pp)

quickCheckN :: QC.Testable prop => Int -> prop -> IO ()
quickCheckN n = QC.quickCheckWith $ QC.stdArgs {QC.maxSuccess = n, QC.maxSize = 100}

-- | Generate a list of valid names for a given type
generateValidNames :: Map LType [Name] -> LType -> ([Name], [Name])
generateValidNames m (UnionType t1 t2) = (l1 ++ l2, u)
  where
    (l1, u) = generateValidNames m t1
    (l2, _) = generateValidNames m t2
generateValidNames m t = (existingVars, undefinedVars)
  where
    existingVars = Data.Maybe.fromMaybe [] (Map.lookup t m)
    undefinedVars = Data.Maybe.fromMaybe [] (Map.lookup NilType m)

-- | Generate a small set of names for generated tests. These names are guaranteed to not include
-- reserved words
genName :: [Name] -> Gen Name
genName = QC.elements

-- | Generate a string literal, being careful about the characters that it may contain
genStringLit :: Gen String
genStringLit = escape <$> QC.listOf (QC.elements stringLitChars)
  where
    -- escape special characters appearing in the string,
    escape :: String -> String
    escape = foldr Char.showLitChar ""
    -- generate strings containing printable characters or spaces, but not including '\"'
    stringLitChars :: [Char]
    stringLitChars = filter (\c -> c /= '\"' && (Char.isSpace c || Char.isPrint c)) ['\NUL' .. '~']

-- | Generate a size-controlled global variable or table field
genVar :: [Name] -> Map LType [Name] -> Int -> LType -> Gen Var
genVar l m 0 t = Name <$> genName l
genVar l m n t = do
  t' <- genType False
  QC.frequency
    [ (1, Name <$> genName l)
      -- (n, genDot l m n' t),
      -- (n, Proj <$> genExp m n' (TableType t' t) <*> genExp m n' t')
    ]
  where
    n' = n `div` 2

-- | Generate a size-controlled dot variable
genDot :: [Name] -> Map LType [Name] -> Int -> LType -> Gen Var
genDot l m n t = case generateValidNames m StringType of
  ([], _) -> genVar l m 0 t
  (l, _) -> Dot <$> genExp m n (TableType StringType t) <*> genName l

-- | Generate a size-controlled typed variable
genTypedVar :: [Name] -> Map LType [Name] -> Int -> LType -> Gen TypedVar
genTypedVar l m n t = liftA2 (,) (genVar l m n t) (pure t)

-- | Generate a size-controlled expression
genExp :: Map LType [Name] -> Int -> LType -> Gen Expression
genExp m 0 t = QC.oneof [genExpVar m 0 t, genVal m 0 t]
genExp m n t =
  QC.frequency
    [ (1, genExpVar m n' t),
      (1, genVal m n' t),
      (n, genUop m n' t),
      (n, genBop m n' t)
      -- (n', genTableFields m n' t)
    ]
  where
    n' = n `div` 2

-- | Generate a size-controlled variable or table field for an expression
genExpVar :: Map LType [Name] -> Int -> LType -> Gen Expression
genExpVar m n t = case generateValidNames m t of
  ([], _) -> genVal m n t
  (l1, l) -> Var <$> genVar l1 m n t

-- | Generate a value
genVal :: Map LType [Name] -> Int -> LType -> Gen Expression
genVal _ _ IntType = Val . IntVal <$> arbitrary
genVal _ _ StringType = Val . StringVal <$> genStringLit
genVal  _ _ BooleanType = Val . BoolVal <$> arbitrary
genVal m n (UnionType t1 t2) = QC.oneof [genVal m n t1, genVal m n t2]
genVal m n t@(TableType t1 t2)= genTableFields m n t
-- genVal m n (FunctionType t1 t2) = undefined
genVal _ _ _ = undefined -- will never reach here

-- | Generate a unary operator
genUop :: Map LType [Name] -> Int -> LType -> Gen Expression
genUop m n IntType = Op1 <$> QC.oneof [pure Neg, pure Len] <*> genExp m n IntType
genUop m n BooleanType = Op1 Not <$> genExp m n BooleanType
genUop m n t = genExpVar m n t -- try to generate a var

-- | Generate a binary operator
genBop :: Map LType [Name] -> Int -> LType -> Gen Expression
genBop m n IntType = Op2 <$>
  genExp m n IntType <*>
  QC.oneof [pure Plus, pure Minus, pure Times, pure Divide, pure Modulo]
  <*> genExp m n IntType
genBop m n StringType = Op2 <$>
  genExp m n StringType <*>
  pure Concat <*>
  genExp m n StringType
genBop m n BooleanType = Op2 <$>
  genExp m n BooleanType <*>
  QC.oneof [pure Eq, pure Gt, pure Ge, pure Lt, pure Le] <*>
  genExp m n BooleanType
genBop m n t = genExpVar m n t -- try to generate a var

-- | Generate a list of fields in a table constructor epression.
-- We limit the size of the table to avoid size blow up.
genTableFields :: Map LType [Name] -> Int -> LType -> Gen Expression
genTableFields m n t@(TableType t1 t2) = do
    len <- QC.elements [1 .. 3]
    TableConst . take len <$> QC.infiniteListOf (genTableField m n t)
genTableFields m n t = genExpVar m n t -- try to generate a var

genTableField :: Map LType [Name] -> Int -> LType -> Gen TableField
genTableField m n (TableType t1 t2) =
  QC.oneof
    [ genFieldName,
      FieldKey <$> genExp m n' t1 <*> genExp m n' t2
    ]
  where
    n' = n `div` 2
    (l1, _) = generateValidNames m t1
    genFieldName = if t1 == StringType && not (null l1)
      then FieldName <$> genName l1 <*> genExp m n' t2
      else FieldKey <$> genExp m n' t1 <*> genExp m n' t2
genTableField _ _ _ = undefined -- will never reach here

-- | Generate a size-controlled statement
genStatement :: Map LType [Name] -> Int -> Gen Statement
genStatement m n | n <= 1 = QC.oneof [genType True >>= genAssign m 0, return Empty]
genStatement m n =
  QC.frequency
    [ (1, genType True >>= genAssign m n'),
      (1, return Empty),
      (n, do
        e <- genExp m n' BooleanType
        b1 <- genBlock m n'
        let updatedMap = updateMapFromIf m b1
        b2 <- genBlock updatedMap n'
        return (If e b1 b2)
      )
      -- -- generate loops half as frequently as if statements
      -- (n', do
      --   let (l1, _) = generateValidNames m BooleanType
      --   if null l1
      --     then return Empty
      --     else While <$> genExpVar m n' BooleanType <*> genBlock m n'
      -- ),
      -- (n', do
      --   let (l1, _) = generateValidNames m BooleanType
      --   if null l1
      --     then return Empty
      --     else Repeat <$> genBlock m n' <*> genExpVar m n' BooleanType
      -- )
    ]
  where
    n' = n `div` 2

-- | Generate a size-controlled assign statement
genAssign :: Map LType [Name] -> Int -> LType -> Gen Statement
genAssign m n t = case generateValidNames m t of
  ([], []) -> return Empty
  (l1, l2) -> Assign <$> genTypedVar (l1 ++ l2) m n t <*> genExp m n t

-- | Generate a size-controlled block
genBlock :: Map LType [Name] -> Int -> Gen Block
genBlock m n = Block <$> genStmts m n
  where
    genStmts :: Map LType [Name] -> Int -> Gen [Statement]
    genStmts _ 0 = pure []
    genStmts m n =
      QC.frequency
        [ (1, return []),
          (n, do
            stmt <- genStatement m n'
            let updatedMap = updateMapFromStatement m stmt
            rest <- genStmts updatedMap n'
            return (stmt : rest)
          )
        ]
      where
        n' = n `div` 2

-- | Update the map of valid names based on the given statement
updateMapFromStatement :: Map LType [Name] -> Statement -> Map LType [Name]
updateMapFromStatement m (Assign (var, varType) _) =
  case var of
    Name name ->
      case Map.lookup varType m of
        Just typeList -> -- Not the first variable of this type
          case Map.lookup NilType m of
            Just nilList ->
              let updatedNilList = filter (/= name) nilList
                  updatedTypeList = name : typeList
              in Map.insert varType updatedTypeList (Map.insert NilType updatedNilList m)
            Nothing -> m  -- NilType not a key
        Nothing -> -- First variable of this type
          case Map.lookup NilType m of
            Just nilList ->
              let updatedNilList = filter (/= name) nilList
              in Map.insert varType [name] (Map.insert NilType updatedNilList m)
            Nothing ->
              Map.insert varType [name] m -- NilType not a key
    _ -> m  -- Nothing to update
updateMapFromStatement m (If _ b1 b2) = updateMapFromIf (updateMapFromIf m b1) b2
  -- in updateMapFromBlock updatedMap b2
updateMapFromStatement m (While _ b) = updateMapFromBlock m b
updateMapFromStatement m (Repeat b _) = updateMapFromBlock m b
updateMapFromStatement m _ = m

-- | Update the map of valid names based on the given block
updateMapFromBlock :: Map LType [Name] -> Block -> Map LType [Name]
updateMapFromBlock m (Block []) = m
updateMapFromBlock m (Block (s : ss)) =
  let updatedMap = updateMapFromStatement m s
  in updateMapFromBlock updatedMap (Block ss)

-- | Update map of valid names after an if statement block
updateMapFromIf :: Map LType [Name] -> Block -> Map LType [Name]
updateMapFromIf m b =
  case Map.lookup NilType (updateMapFromBlock m b) of
    Just l -> Map.insert NilType l m
    Nothing -> m

-- | Generate a size-controlled type
genType :: Bool -> Gen LType
genType False = QC.oneof [return IntType, return StringType, return BooleanType]
genType True =
  QC.oneof
    [ return IntType,
      return StringType,
      return BooleanType,
      TableType <$> genParameterType <*> genType False
      -- FunctionType <$> genParameterType <*> genType False
    ]

-- | Generate a parameter type
genParameterType :: Gen LType
genParameterType =
  QC.oneof
    [ return IntType,
      return StringType,
      return BooleanType,
      UnionType <$> genType False <*> genType False
    ]

instance Arbitrary Var where
  arbitrary = QC.sized $ \size -> do
      ltype <- genType False
      genVar (concat (generateValidNames m ltype)) m size ltype where
    m = Map.singleton NilType (map (:[]) ['a'..'z'])

  shrink (Name n) = []
  shrink (Dot e n) = [Dot e' n | e' <- shrink e]
  shrink (Proj e1 e2) =
    [Proj e1' e2 | e1' <- shrink e1]
      ++ [Proj e1 e2' | e2' <- shrink e2]

instance Arbitrary Statement where
  arbitrary = QC.sized (genStatement m) where
    m = Map.singleton NilType (map (:[]) ['a'..'z'])
  shrink (Assign v e) =
    [Assign v' e | v' <- shrink v]
      ++ [Assign v e' | e' <- shrink e]
  shrink (If e b1 b2) =
    first b1 ++ first b2
      ++ [If e' b1 b2 | e' <- shrink e]
      ++ [If e b1' b2 | b1' <- shrink b1]
      ++ [If e b1 b2' | b2' <- shrink b2]
  shrink (While e b) =
    first b
      ++ [While e' b | e' <- shrink e]
      ++ [While e b' | b' <- shrink b]
  shrink Empty = []
  shrink (Repeat b e) =
    first b
      ++ [Repeat b' e | b' <- shrink b]
      ++ [Repeat b e' | e' <- shrink e]
  shrink (Return e) = undefined

-- | access the first statement in a block, if one exists
first :: Block -> [Statement]
first (Block []) = []
first (Block (x : _)) = [x]

-- | access expressions in a table field
getExp :: TableField -> [Expression]
getExp (FieldName _ e) = [e]
getExp (FieldKey e1 e2) = [e1, e2]

instance Arbitrary TableField where
  arbitrary = QC.sized $ \size -> do
      ltype <- genType False
      genTableField m size ltype where
    m = Map.singleton NilType (map (:[]) ['a'..'z'])
  shrink (FieldName n e1) = [FieldName n e1' | e1' <- shrink e1]
  shrink (FieldKey e1 e2) =
    [FieldKey e1' e2 | e1' <- shrink e1]
      ++ [FieldKey e1 e2' | e2' <- shrink e2]

instance Arbitrary Block where
  arbitrary = QC.sized (genBlock m) where
    m = Map.singleton NilType (map (:[]) ['a'..'z'])

  shrink (Block ss) = []

instance Arbitrary Expression where
  arbitrary = QC.sized $ \size -> do
      ltype <- genType False
      genExp m size ltype where
    m = Map.singleton NilType (map (:[]) ['a'..'z'])

  shrink (Val v) = Val <$> shrink v
  shrink (Var v) = Var <$> shrink v
  shrink (Op1 o e) = e : [Op1 o e' | e' <- shrink e]
  shrink (Op2 e1 o e2) =
    [Op2 e1' o e2 | e1' <- shrink e1]
      ++ [Op2 e1 o e2' | e2' <- shrink e2]
      ++ [e1, e2]
  shrink (TableConst fs) = concatMap getExp fs ++ (TableConst <$> shrink fs)
  shrink (Call fv ps) = undefined

instance Arbitrary Uop where
  arbitrary = QC.arbitraryBoundedEnum

instance Arbitrary Bop where
  arbitrary = QC.arbitraryBoundedEnum

shrinkStringLit :: String -> [String]
shrinkStringLit s = filter (/= '\"') <$> shrink s

instance Arbitrary Value where
  arbitrary =
    QC.oneof
      [ IntVal <$> arbitrary,
        BoolVal <$> arbitrary,
        pure NilVal,
        StringVal <$> genStringLit
        -- note: do not generate table values
      ]

  shrink (IntVal n) = IntVal <$> shrink n
  shrink (BoolVal b) = BoolVal <$> shrink b
  shrink NilVal = []
  shrink (StringVal s) = StringVal <$> shrinkStringLit s
  shrink (TableVal _) = []
  shrink (FunctionVal _ _ _) = []
  shrink (ErrorVal _) = []