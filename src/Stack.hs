module Stack where 


data Stack a = Stack Int [a] deriving (Show)

empty :: Stack a
empty = Stack 0 []

push :: Stack a -> a -> Stack a
push (Stack s xs) item = Stack (s+1) (item : xs)

peek :: Stack a -> Maybe a
peek (Stack _ []) = Nothing
peek (Stack _ (x : xs)) = Just x

pop :: Stack a -> Maybe (Stack a, a)
pop (Stack _ []) = Nothing
pop (Stack s (x : xs)) = Just (Stack (s-1) xs, x)

isEmpty :: Stack a -> Bool
isEmpty (Stack _ []) = True
isEmpty (Stack _ _)  = False

-- | Continue popping until no predicate is true for head. 
popUntil :: Stack a -> (a -> Bool) -> Stack a
popUntil stk@(Stack _ []) f = stk
popUntil stk@(Stack s (x : xs)) f = if f x 
    then stk 
    else popUntil (Stack (s-1) xs) f

-- | Search stack for item by peeking until predicate is true. 
peekUntil :: Stack a -> (a -> Bool) -> Maybe a 
peekUntil (Stack _ []) f = Nothing 
peekUntil (Stack s (x : xs)) f = if f x 
    then Just x 
    else peekUntil (Stack (s-1) xs) f

-- | Peek with offset N. peekN of 0 is same as peek. 
peekN :: Stack a -> Int -> Maybe a 
peekN (Stack _ []) _ = Nothing 
peekN (Stack _ (x : xs)) 0 = Just x 
peekN (Stack s (x : xs)) i = peekN (Stack (s-1) xs) (i-1)


stackSize :: Stack a -> Int
stackSize (Stack s _) = s