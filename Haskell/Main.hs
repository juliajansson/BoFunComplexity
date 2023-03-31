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
computeMinStep = Endo $ \r f -> if isJust (isConst f)
  then zero
  else one + minPWs $ do
    i <- variables f
    let
      [a, b] = do
        (value, factor) <- [(False, mempty), (True, one - mempty)]
        return $ factor * r (setBit (i, value) f)
    return $ a + b

computeMin :: (Show f, BoFun f i, Memoizable f) => f -> PiecewisePoly Rational
computeMin = fix $ appEndo computeMinStep >>> traceMemoize

main :: IO ()
main = printPW $ computeMin $ Threshold.iteratedMaj3 3
