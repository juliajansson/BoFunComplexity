{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE UndecidableInstances #-}
module Threshold where

import Control.Arrow ((>>>), first)
import Control.Monad.Free(Free(..))
import Data.Bifunctor (bimap)
import Data.Either(partitionEithers)
import Data.Function ((&))
import Data.Functor.Classes (Eq1(..), Ord1(..), Show1(..), Eq2(..), Ord2(..), Show2(..), showsBinaryWith)
import Data.Function.Memoize (Memoizable(..), deriveMemoizable, deriveMemoize)
import Data.Maybe (Maybe(..))
import qualified Data.MultiSet as MultiSet
import Prelude hiding ((+), (-), negate)

import DSLsofMath.Algebra (Additive(..), AddGroup(..), (-), sum)

import BoFun
import Util


-- A threshold for a Boolean function.
-- Number of inputs needed for 'True' and 'False' result, respectively.
-- The sum of these thresholds equals the number of inputs plus one.
-- Each threshold is non-negative.
newtype Threshold = Threshold (Square Int)
  deriving (Show, Eq, Ord)

$(deriveMemoizable ''Threshold)

-- Pointwise (via Bool -> Int).
-- TODO: Derive automatically?
instance Additive Threshold where
  zero = Threshold $ tabulateBool $ const zero
  Threshold a + Threshold b = Threshold $ tabulateBool $ \i -> lookupBool a i + lookupBool b i

instance AddGroup Threshold where
  negate (Threshold t) = Threshold $ tabulateBool $ lookupBool t >>> negate

-- TODO: What would be the type class for an algebra over the integers?
thresholdScale :: Int -> Threshold -> Threshold
thresholdScale x (Threshold t) = Threshold $ tabulateBool $ lookupBool t >>> (x *)

thresholdNumInputs :: Threshold -> Int
thresholdNumInputs (Threshold (nt, nf)) = nt + nf - 1

-- A constant threshold (fixed result).
thresholdConst :: Bool -> Threshold
thresholdConst v = Threshold $ tabulateBool ((== v) >>> boolToInt)

thresholdIsConst :: Threshold -> Maybe Bool
thresholdIsConst (Threshold (nt, nf)) = if
  | nt <= 0 -> Just True
  | nf <= 0 -> Just False
  | otherwise -> Nothing

thresholdFair :: Int -> Threshold
thresholdFair = duplicate >>> Threshold


-- A threshold-type Boolean function.
data ThresholdFun f = ThresholdFun {
  threshold :: Threshold,
  -- The subfunctions.
  -- None of the subfunctions are constant.
  -- Normalization condition: if one of the thresholds is zero, then there are no subfunctions.
  thresholdFunctions :: MultiSet.MultiSet f
} deriving (Show)

-- Necessitated by misdesign of Haskell typeclasses.
instance Eq1 ThresholdFun where
  liftEq eq' (ThresholdFun t us) (ThresholdFun t' us') = liftEq2 (==) (liftEq eq') (t, us) (t', us')

instance Ord1 ThresholdFun where
  liftCompare compare' (ThresholdFun t us) (ThresholdFun t' us') = liftCompare2 compare (liftCompare compare') (t, us) (t', us')

-- TODO: use record fields.
instance Show1 ThresholdFun where
  liftShowsPrec showsPrec' showList' p (ThresholdFun t u) = showsBinaryWith showsPrec (liftShowsPrec showsPrec' showList') "ThresholdFun" p t u

-- TODO: instance Read1 ThresholdFun

{-
TODO:
Figure out why this doesn't work.
The error message is:
    • ‘Threshold’ is not in the type environment at a reify
    • In the untyped splice: $(deriveMemoize ''ThresholdFun)
-}
-- instance (Ord x, Memoizable x) => Memoizable (ThresholdFun x) where
--   memoize = $(deriveMemoize ''ThresholdFun)

-- TODO: Special case of transport of a type class along an isomorphism.
instance (Ord x, Memoizable x) => Memoizable (ThresholdFun x) where
  memoize f = m >>> memoize (n >>> f) where
    -- Back and forth.
    m (ThresholdFun t us) = (t, us)
    n (t, us) = ThresholdFun t us

thresholdFunConst :: Bool -> ThresholdFun f
thresholdFunConst val = ThresholdFun (thresholdConst val) MultiSet.empty

-- Normalizes threshold functions equivalent to a constant function.
thresholdFunNormalize :: (Eq f, BoFun f i) => ThresholdFun f -> ThresholdFun f
thresholdFunNormalize u = case thresholdIsConst (threshold u) of
  Just val -> ThresholdFun (thresholdConst val) MultiSet.empty
  Nothing -> u

-- Reduces constant subfunctions in a threshold function.
-- Not used for anything right now.
{-
thresholdFunNormalizeSub :: (Eq f, BoFun f i) => ThresholdFun f -> ThresholdFun f
thresholdFunNormalizeSub (ThresholdFun t us) = ThresholdFun (t - s) (MultiSet.fromAscOccurList us') where
  (reduced, us') = us
    & MultiSet.toOccurList
    & map (first viewConst >>> (\(x, k) -> bimap (, k) (, k) x))
    & partitionEithers
  s = reduced
    & map (\(val, k) -> thresholdScale k (thresholdConst val))
    & sum
-}

-- TODO: Figure out why this needs UndecidableInstances. (Haskell...)
instance (Ord f, BoFun f i) => BoFun (ThresholdFun f) (Int, i) where
  isConst = threshold >>> thresholdIsConst

  variables (ThresholdFun _ us) = do
    (i, (u, _)) <- us & MultiSet.toAscOccurList & zip naturals
    v <- variables u
    return (i, v)

  setBit ((i, v), val) (ThresholdFun t us) = case isConst u' of
    Just val -> thresholdFunNormalize $ ThresholdFun t' us'
    Nothing -> ThresholdFun t $ MultiSet.insert u' us'
    where
    (u, _) = MultiSet.toAscOccurList us !! i
    us' = us & MultiSet.delete u
    u' = setBit (v, val) u
    t' = t - thresholdConst val

-- A thresholding function with copies of a single subfunction.
thresholdFunReplicate :: (Ord f) => Threshold -> f -> ThresholdFun f
thresholdFunReplicate t u = ThresholdFun t $ MultiSet.fromOccurList [(u, thresholdNumInputs t)]


-- Boolean functions built from iterated thresholding.
type IteratedThresholdFun f = Free ThresholdFun f

-- Could special case the above type to avoid pulling in the Kmettiverse.
-- data IteratedThresholdFun f = Pure f | Free (IteratedThresholdFun (IteratedThresholdFun f))
--   deriving (Show, Eq, Ord)

instance (Ord f, Memoizable f) => Memoizable (IteratedThresholdFun f) where
  memoize = $(deriveMemoize ''Free)

iteratedThresholdFunConst :: Bool -> IteratedThresholdFun f
iteratedThresholdFunConst = thresholdFunConst >>> Free

{-
-- General instance.
-- Conflicts with the specialized instance for IteratedThresholdFun' given below.
instance (Ord f, BoFun f i) => BoFun (IteratedThresholdFun f) ([Int], i) where
  isConst (Pure u) = isConst u
  isConst (Free v) = isConst v

  variables (Pure u) = variables u & map ([],)
  variables (Free v) = variables v & map (\(i, (is, j)) -> (i : is, j))

  setBit (([], j), val) (Pure u) = Pure $ setBit (j, val) u
  setBit ((i : is, j), val) (Free v) = Free $ setBit ((i, (is, j)), val) v
-}

type IteratedThresholdFun' = IteratedThresholdFun ()

instance BoFun IteratedThresholdFun' [Int] where
  isConst (Pure ()) = Nothing
  isConst (Free u) = isConst u

  variables (Pure ()) = [[]]
  variables (Free v) = variables v & map (uncurry (:))

  setBit ([], val) (Pure u) = iteratedThresholdFunConst val
  setBit (i : is, val) (Free v) = Free $ setBit ((i, is), val) v


-- Example Boolean functions.

maj5 :: ThresholdFun (Maybe Bool)
maj5 = thresholdFunReplicate (thresholdFair 3) Nothing

iteratedMaj3 :: Int -> IteratedThresholdFun'
iteratedMaj3 0 = Pure ()
iteratedMaj3 n = Free $ thresholdFunReplicate (thresholdFair 2) $ iteratedMaj3 $ n - 1

iteratedMaj5 :: Int -> IteratedThresholdFun'
iteratedMaj5 0 = Pure ()
iteratedMaj5 n = Free $ thresholdFunReplicate (thresholdFair 3) $ iteratedMaj5 $ n - 1


{-
The number s_n of nodes reachable from iteratedMaj3 n is given by the following recurrence:
* s_0 = 3,
* s_{n+1} = 2 + (s_n + 5) s_n (s_n - 2) / 6.
For example:
* s_0 = 3,
* s_1 = 6
* s_2 = 46,
* s_3 = 17206,
* s_4 = 849110490846.

This can be checked for s <= 3 as follows:

>>> [0..3] & map (iteratedMaj3 >>> reachable >>> length)
[3,6,46,17206]
-}
