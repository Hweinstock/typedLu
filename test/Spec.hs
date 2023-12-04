import Test.HUnit
import Test.QuickCheck
-- import qualified LuStepper as LS
-- import qualified LuParser  as LP
import qualified LuParserTest as LP
import qualified LuEvaluatorTest as LE
import qualified LuStepperTest as LS
import qualified LuE2ETest as LE2E
import qualified LuTypeCheckerTest as LTC

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
