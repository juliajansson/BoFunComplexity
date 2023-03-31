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
computeMin = fix $ appEndo computeMinStep >>> traceMemoize

maj3_3 :: PiecewisePoly Rational
maj3_3 = computeMin $ Threshold.iteratedMaj3 3

main :: IO ()
main = printPW $ maj3_3

maj5_2 = computeMin $ Threshold.iteratedMaj5 2
