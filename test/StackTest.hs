module StackTest where

import Stack
import Test.HUnit
  ( Counts,
    Test (TestList),
    runTestTT,
    (~:),
    (~?=),
  )
import Test.QuickCheck qualified as QC

test_empty :: Test
test_empty =
  "test empty"
    ~: TestList
      [ isEmpty empty ~?= True,
        isEmpty (push empty 5) ~?= False,
        stackSize empty ~?= 0
      ]

test_push :: Test
test_push =
  "test push"
    ~: TestList
      [ stackSize (push empty 5) ~?= 1,
        stackSize (push (push empty 5) 5) ~?= 2,
        stackSize (push (push (push empty 5) 5) 5) ~?= 3
      ]

test_peek :: Test
test_peek =
  "test peek"
    ~: TestList
      [ peek (push empty 5) ~?= Just 5,
        peek (empty :: Stack Int) ~?= Nothing
      ]

test_pop :: Test
test_pop =
  "test peek"
    ~: TestList
      [ pop (push empty 5) ~?= Just (empty, 5),
        pop (empty :: Stack Int) ~?= Nothing
      ]

test_popUntil :: Test
test_popUntil =
  "test popUntil"
    ~: TestList
      [ popUntil (fromList [1, 2, 3, 4, 5, 6]) (3 <) ~?= fromList [4, 5, 6],
        popUntil (fromList [1, 2, 3, 4, 5, 6]) (const True) ~?= fromList [1, 2, 3, 4, 5, 6],
        popUntil (fromList [1, 2, 3, 4, 5, 6]) (const False) ~?= empty,
        popUntil (empty :: Stack Int) (const True) ~?= (empty :: Stack Int),
        popUntil (empty :: Stack Int) (const False) ~?= (empty :: Stack Int)
      ]

test_peekUntil :: Test
test_peekUntil =
  "test peekUntil"
    ~: TestList
      [ peekUntil (fromList [1, 2, 3, 4, 5, 6]) (3 <) ~?= Just 4,
        peekUntil (fromList [1, 2, 3, 4, 5, 6]) (const False) ~?= Nothing,
        peekUntil (fromList [1, 2, 3, 4, 3, 6]) (== 3) ~?= Just 3,
        peekUntil (empty :: Stack Int) (const True) ~?= Nothing,
        peekUntil (empty :: Stack Int) (const False) ~?= Nothing
      ]

test_peekN :: Test
test_peekN =
  "test peekN"
    ~: TestList
      [ peekN (fromList [1, 2, 3, 4, 5, 6]) 3 ~?= Just 4,
        peekN (fromList [1, 2, 3, 4, 5, 6]) 6 ~?= Nothing,
        peekN (fromList [1, 2, 3, 4, 3, 6]) 0 ~?= Just 1,
        peekN (empty :: Stack Int) 2 ~?= Nothing,
        peekN (empty :: Stack Int) 0 ~?= Nothing
      ]

test :: IO Counts
test = runTestTT $ TestList [test_peekN, test_peekUntil, test_popUntil, test_peek, test_push, test_empty, test_pop]

prop_toListfromList :: [Int] -> Bool
prop_toListfromList lst = lst == toList (fromList lst)

prop_peekAfterPush :: [Int] -> Int -> Bool
prop_peekAfterPush lst x = let stk = fromList lst in peek (push stk x) == Just x

prop_popAfterPush :: [Int] -> Int -> Bool
prop_popAfterPush lst x = let stk = fromList lst in pop (push stk x) == Just (stk, x)

qc :: IO ()
qc = do
  putStrLn "prop_toListfromList"
  QC.quickCheck prop_toListfromList
  putStrLn "prop_peekAfterPush"
  QC.quickCheck prop_peekAfterPush
  putStrLn "prop_popAfterPush"
  QC.quickCheck prop_popAfterPush