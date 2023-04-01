module Main where

import Control.Arrow((>>>))
import Data.Function (fix)
import Data.Function.Memoize (Memoizable(..), traceMemoize, memoFix)
import Data.Maybe (isJust)
import Data.Monoid (Endo(..))
import Debug.Trace (trace)
import Prelude hiding ((+), (-), (*))

import DSLsofMath.Algebra

import BoFun
import PiecewisePoly
import Threshold

computeMinStep :: (Show f, BoFun f i) => Endo (f -> PiecewisePoly Rational)
computeMinStep = Endo $ \recCall fun -> if isJust (isConst fun)
  then zero
  else one + minPWs $ do
    i <- variables fun
    let
      [a, b] = do
        (value, factor) <- [(False, mempty), (True, one - mempty)]
        return $ factor * recCall (setBit (i, value) fun)
    return $ a + b

computeMin :: (Show f, BoFun f i, Memoizable f) => f -> PiecewisePoly Rational
computeMin = fix $ appEndo computeMinStep >>> memoize

maj3_3 :: PiecewisePoly Rational
maj3_3 = computeMin $ Threshold.iteratedMaj3 3

-- This has a single piece:
-- * P [9,9,9,30,12,62,-14,816,-2143,-44004,169768,-291977,751873,-2494791,5464225,-8722210,13579067,-21830058,29475938,-29211477,20338155,-9697875,3027801,-559872,46656]
maj5_2 :: PiecewisePoly Rational
maj5_2 = computeMin $ Threshold.iteratedMaj5 2

main :: IO ()
main = do
  putStrLn $ "maj5_2: " ++ showPW maj5_2
  putStrLn $ "maj3_3: " ++ showPW maj3_3
