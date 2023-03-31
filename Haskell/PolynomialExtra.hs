{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE DeriveFunctor #-}
module PolynomialExtra where

import Control.Arrow ((>>>), (***), second)
import Data.Maybe (isJust)
import Data.Ratio (Ratio(..), (%), numerator, denominator)
import Prelude hiding ((+), (-), (*), negate, recip, quot)
import qualified Prelude ((*))

import DSLsofMath.Algebra
import DSLsofMath.PSDS

import Util


-- The compositional monoidal structure.
instance (Ring a) => Semigroup (Poly a) where
  (<>) = comP

instance (Ring a) => Monoid (Poly a) where
  mempty = xP

scalar :: (Ring a) => a -> Poly a
scalar = flip scaleP one

viewLow :: Ring a => Int -> Poly a -> [a]
viewLow n (P cs) = take n (cs ++ Prelude.repeat zero)

evalZero :: Ring a => Poly a -> a
evalZero (P cs) = case cs of
  [] -> zero
  a : as -> a

lowestNonzero :: (Eq a, Ring a) => Poly a -> a
lowestNonzero (P cs) = h cs where
  h [] = zero
  h (a : as) | a == zero = h as
             | otherwise = a


-- Some transformations.

reverseCoeff :: (Eq a, Additive a) => Poly a -> Poly a
reverseCoeff = normalPoly >>> unP >>> reverse >>> P

-- Precomposes the given polynomial with multiplication by the given factor.
scaleInput :: Ring a => a -> Poly a -> Poly a
scaleInput c = unP >>> h one >>> P
  where
  h k [] = []
  h k (x : xs) = k * x : h (c * k) xs

-- Precomposes the given polynomial with addition by the given factor.
translateInput :: Ring a => a -> Poly a -> Poly a
translateInput c = (`comP` P [c, one])

-- Reparametrize by flipping the unit interval around.
flipUnitIntervalPoly :: (Ring a) => Poly a -> Poly a
flipUnitIntervalPoly = (`comP` P [one, negate one])


-- Descartes' rule of sign.

-- Sign changes of a non-zero polynomial, including counts of initial zero coefficients
signChanges :: (Ord a, Additive a) => Poly a -> Int
signChanges = unP >>> map (`compare` zero) >>> signChanges' where

  signChanges' :: [Ordering] -> Int
  signChanges' [] = 0
  signChanges' (c:cs) | c == EQ = 1 + signChanges' cs
                      | otherwise = signChanges'' c cs

  signChanges'' :: Ordering -> [Ordering] -> Int
  signChanges'' _ [] = 0
  signChanges'' a (c:cs) | c `elem` [EQ, a] = signChanges'' a cs
                         | otherwise = 1 + signChanges'' c cs

-- Decartes upper bound for zeroes.
-- The half-open interval is specified by basepoint.
-- * True: [0, 1)
-- * False: (0, 1]
-- Returns 0 on zero.
descartes :: (Ord a, Ring a) => Bool -> Poly a -> Int
descartes basepoint =
      (if basepoint then flipUnitIntervalPoly else id)
  >>> reverseCoeff
  >>> translateInput one
  >>> normalPoly
  >>> signChanges

-- Checks if the given square-free polynomial has a root in [0, 1).
-- Condition: the polynomial has at most one root in this interval.
squarefreeRoot :: (Ord a, Ring a) => Bool -> Poly a -> Bool
squarefreeRoot basepoint = descartes basepoint >>> odd


-- Affine polynomials.
data AffinePoly a = AffinePoly
  a  -- scale factor
  a  -- offset
  deriving (Eq, Ord, Show, Functor)

affinePoly :: AffinePoly a -> Poly a
affinePoly (AffinePoly scale offset) = P [offset, scale]

affineFromPoly :: (Ring a) => Poly a -> AffinePoly a
affineFromPoly p = AffinePoly scale offset where
  [offset, scale] = viewLow 2 p

instance (Ring a) => Semigroup (AffinePoly a) where
  a <> b = affineFromPoly $ comP (affinePoly a) (affinePoly b)

instance (Ring a) => Monoid (AffinePoly a) where
  mempty = affineFromPoly xP

instance (Field a) => Group (AffinePoly a) where
  invert (AffinePoly scale offset) = AffinePoly scale' offset' where
    scale' = recip scale
    offset' = negate $ scale' * offset


-- Relating rational and integral polynomials.

content :: (Euclidean a) => Poly a -> a
content = content' . unP

-- Sometimes more efficient.
contentFromHighest :: (Euclidean a) => Poly a -> a
contentFromHighest = content' . reverse . unP

content' :: (Euclidean a) => [a] -> a
content' [] = zero
content' (x : xs) = r where
  (r, _) = generator (x, content' xs)

normalRationalPoly :: (Euclidean a) => Poly a -> Poly a
normalRationalPoly (P xs) = P $ map (`quot` r) xs where
  r = content' xs

-- Also returns the scaling factor.
-- Integral and ring instances must agree.
makeIntegral :: (Prelude.Integral a, Ring a) => Poly (Ratio a) -> (a, Poly a)
makeIntegral = unP >>> makeIntegral' >>> second P where

  makeIntegral'' :: (Prelude.Integral a) => Ratio a -> (a, a)
  makeIntegral'' x = (denominator x, numerator x)

  makeIntegral' :: (Prelude.Integral a, Ring a) => [Ratio a] -> (a, [a])
  makeIntegral' [] = (one, [])
  makeIntegral' (c : cs) = (x * y, c'' : cs'') where
    (x, cs') = makeIntegral' cs
    c' = (x % 1) Prelude.* c
    (y, c'') = makeIntegral'' c'
    cs'' = scaleL y cs'


-- Regarding GCD.

gcdMany :: (Field a, Eq a) => [Poly a] -> Poly a
gcdMany = Prelude.foldr1 gcdP

radical' :: (Show a, Field a, Eq a) => Poly a -> Poly a
radical' = yun >>> foldr (*) one

radical :: (Show a, Field a, Eq a) => Poly a -> Poly a
radical p = if
  | p == zero -> zero
  | otherwise -> radical' p

{- Unfinished: rational GCD with integral coefficients.
rationalGenerator :: (Euclidean a) => (Poly a, Poly a) -> (Poly a, (Poly a, Poly a))
rationalGenerator (x, y) = if
  | y' <- normalPoly y, y' == zero -> (x, (one, zero))
  | otherwise -> undefined

reduce :: (Euclidean a) => (Int, [a]) -> (Int, [a])
reduce (n, xs) = (n', xs') where
  (xz, xs') = Prelude.span (== zero) xs
  n' = n - length xz

rationalGenerator' :: (Euclidean a) => ((Int, [a]), (Int, [a])) -> ([a], ([a], [a]))
rationalGenerator' (x@(xn, xs), yp) =
  if xn < yn'
  then let
    (r, (b, a)) = rationalGenerator' (y, x) in
    (r, (a, b))
  else case ys of
    [] -> (xs, ([one], []))
    yl : ys' -> case xs of
      xl : xs' -> let
        (r, _) = generator xl yl
        xl' = quot xl r
        yl' = quot yl r
        zn = xn - 1
        zs = addL (scaleL yl' xs') (scaleL (neg xl') ys')
        (r, (b, c)) = rationalGenerator' y (zn, zs)
        in
        (r, ())
  where
  y@(yn, ys) = reduce yp
-}


-- TODO: move below to algebra module.

equalRatio :: (Eq a, Ring a) => [(a, a)] -> Maybe (a, a)
equalRatio [] = Nothing
equalRatio (r@(a_0, a_1) : rs) = case equalRatio rs of
  Nothing -> Just r
  Just (b_0, b_1)
    | a_0 * b_1 == b_0 * a_1 -> Just r
    | otherwise -> Nothing

similar' :: (Eq a, Ring a) => (Poly a, Poly a) -> Bool
similar' = (unP *** unP) >>> zipZero >>> equalRatio >>> isJust

-- Determine if two polynomials are the same over the rationals up to units.
similar :: (Eq a, Ring a) => (Poly a, Poly a) -> Bool
similar (p, q) = p == q || similar' (p, q) where

viewZero :: (Additive a) => [a] -> (a, [a])
viewZero [] = (zero, [])
viewZero (x : xs) = (x, xs)

zipZero :: (Additive a) => ([a], [a]) -> [(a, a)]
zipZero ([], []) = []
zipZero (xs, ys) = (x, y) : zipZero (xs', ys')
  where
  (x, xs') = viewZero xs
  (y, ys') = viewZero ys
