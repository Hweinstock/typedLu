-- import qualified LuStepper as LS
-- import qualified LuParser  as LP

import LuE2ETest qualified as LE2E
import LuEvaluatorTest qualified as LE
import LuParserTest qualified as LP
import LuStepperTest qualified as LS
import LuTypeCheckerTest qualified as LTC
import Test.HUnit
import Test.QuickCheck

main :: IO ()
main = do
  putStrLn "\n*** Testing LuParser ***"
  LP.test
  LP.qc
  putStrLn "\n*** Testing LuEvaluator ***"
  LE.test
  LE.qc
  putStrLn "\n*** Testing LuStepper ***"
  LS.test
  LS.qc
  putStrLn "\n*** Testing LuTypeChecker ***"
  LTC.test
  LTC.qc
  putStrLn "\n*** Testing LuE2ETest ***"
  LE2E.test
  putStrLn "*** Done Testing ***"
