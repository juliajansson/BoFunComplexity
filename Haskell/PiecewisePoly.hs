{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE DeriveFunctor #-}
module PiecewisePoly where

import Control.Applicative (Applicative(..))
import Control.Arrow ((>>>), (***))
import Control.Monad (forM_, guard)
import Data.Bifunctor (Bifunctor(..), bimap)
import Data.Function ((&))
import Data.Maybe (fromMaybe)
import Data.Ratio ((%), numerator)
import qualified Data.Set as S (Set, fromList, size)
import Debug.Trace (trace, traceShow)
import Prelude hiding (Num(..),Fractional(..), fromIntegral, min, sum, product)
import qualified Prelude

import DSLsofMath.Algebra
import DSLsofMath.PSDS (Poly(P,unP), evalP, degree, comP, gcdP)

import Util
import PolynomialExtra


-- Zoom data:
-- Affine transformations stratified into levels.
-- The intended use case is iterated reparametrizations of halves of the unit interval (and possibly their inverses).
-- Here, the scale is two to the power of the negated zoom level.
data ZoomData a = ZoomData {
  zoomLevel :: Int,               -- TODO: decide if we want that here
  zoomAffinePoly :: AffinePoly a  -- affine transformation
} deriving (Eq, Ord, Show, Functor)

instance (Ring a) => Semigroup (ZoomData a) where
  ZoomData l0 a0 <> ZoomData l1 a1 = ZoomData (l0 + l1) (a0 <> a1)

instance (Ring a) => Monoid (ZoomData a) where
  mempty = ZoomData 0 (affineFromPoly mempty)

instance (Field a) => Group (ZoomData a) where
  invert (ZoomData l a) = ZoomData (-l) (invert a)

zoomEval :: (Ring a) => ZoomData a -> a -> a
zoomEval = zoomAffinePoly >>> affinePoly >>> evalP


-- TODO: memoize
zoomHalf :: (Field a) => Bool -> ZoomData a
zoomHalf bp = ZoomData 1 $ AffinePoly (one / two) $ if bp then zero else one / two

zoomLeft :: (Field a) => ZoomData a
zoomLeft = zoomHalf True

zoomRight :: (Field a) => ZoomData a
zoomRight = zoomHalf False


-- Right zoom algebras.
class Ring a => Zoomable a x | x -> a where
  zoom :: ZoomData a -> x -> x

-- Just Haskell stuff: can't give zoomable instance for unit type.
-- Also, this seems to conflict with other instances.
--instance (Zoomable a x, Zoomable b x) => Zoomable (a, b) x where
--  zoom z (a, b) = (zoom z a, zoom z b)

-- Yoneda embedding.
instance (Ring a) => Zoomable a (ZoomData a) where
  zoom z z' = z' <> z

-- TODO: why is UndecidableInstances needed here?
instance (Ring a) => Zoomable a (Poly a) where
  zoom (ZoomData _ t) = (`comP` affinePoly t)


-- The graph of the counit map of free Zoom algebra adjunction.
data Zoomed a x = Zoomed
  { original :: x           -- the data at original scale
  , zoomData :: ZoomData a  -- the zoom
  , zoomed :: x             -- the zoomed data
  } deriving (Eq, Ord, Show)

instance Functor (Zoomed a) where
  fmap f (Zoomed original z zoomed) = Zoomed (f original) z (f zoomed)

instance Bifunctor Zoomed where
  bimap f g (Zoomed original z zoomed) = Zoomed (g original) (fmap f z) (g zoomed)

-- Really this is an instance of Applicative for each fixed zoomData attribute.
instance Applicative (Zoomed a) where
  pure x = Zoomed x undefined x
  Zoomed fOrig z fZoomed <*> Zoomed xOrig _ xZoomed = Zoomed (fOrig xOrig) z (fZoomed xZoomed) 

-- Zoomed a is a pointed functor.
zoomedTrivial :: (Ring a) => x -> Zoomed a x
zoomedTrivial v = Zoomed v mempty v

zoomedGenerate :: (Zoomable a x) => ZoomData a -> x -> Zoomed a x
zoomedGenerate z v = Zoomed v z $ zoom z v

instance (Zoomable a x) => Zoomable a (Zoomed a x) where
  zoom z (Zoomed original z' zoomed) = Zoomed original (zoom z z') (zoom z zoomed)

-- Requirement: zooming preserves the additive structure.
class (Zoomable a x, AddGroup x) => ZoomableAddGroup a x

instance (Ring a) => ZoomableAddGroup a (Poly a)

-- These are really instances fibred over a given zoom data.
instance (ZoomableAddGroup x a) => Additive (Zoomed x a) where
  zero = undefined
  Zoomed o0 d z0 + Zoomed o1 _ z1 = Zoomed o d z where
    o = o0 + o1
    z = z0 + z1

instance (ZoomableAddGroup x a) => AddGroup (Zoomed x a) where
  negate (Zoomed o d z) = Zoomed (negate o) d (neg z)


-- Approximations to values that turn into the exact values below a given zoom levle.
data ZoomedApprox a x = ZoomedApprox {
  approxValue :: Zoomed a x,     -- current value
  approxInfo  :: Maybe (Int, x)  -- if current value is approximation: level bound below it is to be used and actual value
} deriving (Show)

viewApprox :: ZoomedApprox a x -> Zoomed a x
viewApprox = approxValue

approxTrueOrig :: ZoomedApprox a x -> x
approxTrueOrig (ZoomedApprox v m) = case m of
  Nothing -> original v
  Just (_, x) -> x

normalizeApprox :: (Zoomable a x) => ZoomedApprox a x -> ZoomedApprox a x
normalizeApprox approx@(ZoomedApprox value m) = h where
  valueZD@(ZoomData level _) = zoomData value
  h = case m of
    Just (limit, exactOriginal) | level >= limit -> ZoomedApprox (zoomedGenerate valueZD exactOriginal) Nothing
    _ -> approx

instance Functor (ZoomedApprox a) where
  fmap f (ZoomedApprox value m) = ZoomedApprox (fmap f value) (fmap (fmap f) m)

-- There are two evident Zoomable instances.
-- The functorial one that doesn't normalize and the one given here.
instance (Show a, Show x, Zoomable a x) => Zoomable a (ZoomedApprox a x) where
  zoom z (ZoomedApprox value m) = mayTrace ("zoomApprox " ++ show z ++ " with result " ++ show r) r where
    r = normalizeApprox $ ZoomedApprox (zoom z value) m


type ZoomedPoly a = Zoomed a (Poly a)
type ZoomedApproxPoly a = ZoomedApprox a (Poly a)

radicalApprox :: (Show a, Field a, Ord a) => ZoomedPoly a -> ZoomedApproxPoly a
radicalApprox v@(Zoomed p _ _) = normalizeApprox $ ZoomedApprox v $ Just (5 + degree p, radical p)

gcdApprox :: (Field a, Ord a) => [ZoomedPoly a] -> ZoomedApproxPoly a
gcdApprox xs = normalizeApprox $ ZoomedApprox (zoomedGenerate (zoomData (head xs)) one) $ Just (3 + (sum (map degree ps) `div` length xs), gcdMany ps)
  where
  ps = map original xs

radicalGCDApprox :: (Show a, Field a, Ord a) => [ZoomedPoly a] -> ZoomedApproxPoly a
radicalGCDApprox xs = normalizeApprox $ ZoomedApprox (zoomedGenerate (zoomData (head xs)) one) $ Just (3 + (sum (map degree ps) `div` length xs), radical $ gcdMany ps)
  where
  ps = map original xs


bisected' :: (Field a, Zoomable a x) => Bool -> x -> x
bisected' = zoom . zoomHalf

bisected :: (Field a, Zoomable a x) => x -> (x, x)
bisected = tabulateBool . flip bisected'


type Intersect a = (ZoomedPoly a, (ZoomedPoly a, ZoomedPoly a))

{-
A piecewise polynomial at some zoom level.
The domain of definition is rescaled to [0, 1).

Invariants:
* PWBisect right composes current zoom according to 'bisected'.
* In the linearization, neighbouring polynomials are equal.

Intersections at 0 are captured by PWIntersect.

TODO:
Investigate if we should move back to a symmetric version ([0, 1]).
There, intersections at 0 and 1 are ignored.
And an intersection at 1/2 is captures by different polynomials in each half.
* May avoid GCD operations for common multiple roots.
* Allows us to divide out zeros at 0.
-}
data PiecewisePoly a =
    PWPoly (ZoomedPoly a)
  | PWIntersect (Intersect a)
  | PWBisect (Square (PiecewisePoly a))
  deriving (Show)

instance Functor PiecewisePoly where
  fmap f p = case p of
    PWPoly p -> PWPoly $ f' p
    PWIntersect (r, ps) -> PWIntersect (f' r, tabulateBool $ lookupBool ps >>> f')
    PWBisect ps -> PWBisect $ tabulateBool $ lookupBool ps >>> fmap f
    where
    f' = bimap f (fmap f)

pwCheckZoomData :: (Field a, Eq a) => ZoomData a -> PiecewisePoly a -> Maybe ()
pwCheckZoomData z p = case p of
  PWPoly p -> check p
  PWIntersect (r, (p_0, p_1)) -> forM_ [r, p_0, p_1] check
  PWBisect p -> forM_ [True, False] $ \i -> pwCheckZoomData (bisected' i z) (lookupBool p i)
  where
  check p = guard $ zoomData p == z

isPoly :: PiecewisePoly a -> Bool
isPoly (PWPoly _) = True
isPoly _ = False

piecewiseFromPoly :: (Ring a) => Poly a -> PiecewisePoly a
piecewiseFromPoly = zoomedTrivial >>> PWPoly

-- TODO: Find better return type.
linearizePW' :: (Field a) => ZoomData a -> PiecewisePoly a -> [Either (Poly a) (Poly a, Square a)]
linearizePW' z p = case p of
  PWPoly p -> [Left $ original p]
  PWIntersect (r, (p_0, p_1)) ->
    [ Left $ original p_0
    , Right (original r, (zoomEval z zero, zoomEval z one))
    , Left $ original p_1
    ]
  PWBisect p -> [True, False]
    & fmap (\i -> linearizePW' (bisected' i z) (lookupBool p i))
    & mconcat

normalizePWLinear :: (Eq a) => [Either a b] -> [Either a b]
normalizePWLinear (Left p : xs) = h p xs where
  h p [] = [Left p]
  h p (Left p' : xs) | p == p' = h p xs
  h p (Right q : Left p' : xs) = Left p : Right q : h p' xs

linearizePW :: (Field a, Eq a) => PiecewisePoly a -> [Either (Poly a) (Poly a, Square a)]
linearizePW = linearizePW' mempty >>> normalizePWLinear

-- Old special case:
--  | evalZero (zoomed r_r) == zero -> (PWPoly p_0_l, PWPoly p_1_r)
bisectedIntersect :: (Field a, Ord a) => Intersect a -> Square (PiecewisePoly a)
bisectedIntersect (r, (p_0, p_1)) = if squarefreeRoot True (zoomed r_l)
  then (PWIntersect (r_l, (p_0_l, p_1_l)), PWPoly p_1_r)
  else (PWPoly p_0_l, PWIntersect (r_r, (p_0_r, p_1_r)))
  where
  (r_l, r_r) = bisected r
  (p_0_l, p_0_r) = bisected p_0
  (p_1_l, p_1_r) = bisected p_1

bisectedPW :: (Field a, Ord a) => PiecewisePoly a -> Square (PiecewisePoly a)
bisectedPW (PWBisect x) = x
bisectedPW (PWPoly p) = (PWPoly *** PWPoly) $ bisected p
bisectedPW (PWIntersect x) = bisectedIntersect x

evalPW' :: (Field a, Ord a) => ZoomData a -> PiecewisePoly a -> a -> a
evalPW' z p x = case p of
  PWPoly p -> evalP (original p) x
  PWIntersect (r, ps) -> if evalP (original r) x == zero
    then uncurry unify $ tabulateBool $ lookupBool ps >>> ev
    else deepen
  PWBisect p -> deepen
  where
  ev p = evalP (original p) x
  s = invert >>> zoomAffinePoly >>> affinePoly >>> (`evalP` x)
  i = s (zoom zoomLeft z) < one
  deepen = evalPW' (bisected' i z) (lookupBool (bisectedPW p) i) x

evalPW :: (Field a, Ord a) => PiecewisePoly a -> a -> a
evalPW = evalPW' mempty


normalizedBisect :: (Show a, Ring a, Ord a) => ZoomData a -> Square (PiecewisePoly a) -> PiecewisePoly a
normalizedBisect z p = if
  | (PWPoly p_0, PWPoly p_1) <- p, original p_0 == original p_1 -> PWPoly (g p_0)
  | (PWPoly p_0, PWIntersect (r, (p_10, p_11))) <- p, original p_0 == original p_10, Just _ <- comparePoly (f p_10) (f p_11) (f r) -> PWIntersect (g r, (g p_10, g p_11))
  | (PWIntersect (r, (p_00, p_01)), PWPoly p_1) <- p, original p_1 == original p_01, Just _ <- comparePoly (f p_00) (f p_01) (f r) -> PWIntersect (g r, (g p_00, g p_01))
  | otherwise -> PWBisect p
  where
  f = original >>> zoom z
  g = original >>> zoomedGenerate z

normalizedBisect' :: (Show a, Field a, Ord a) => ZoomData a -> (Bool -> PiecewisePoly a) -> PiecewisePoly a
normalizedBisect' z f = normalizedBisect z (f True, f False)

normalizedIntersect :: (Show a, Ring a, Eq a) => Intersect a -> PiecewisePoly a
normalizedIntersect p@(r, (p_0, p_1)) = res where
  res = if original p_0 == original p_1
    then PWPoly p_0
    else PWIntersect p
  res' | original p_0 - original p_1 `elem` [original r, negate $ original r] = res
       | otherwise = error $ "THE STRANGEST THING: " ++ show (original p_0) ++ ", " ++ show (original p_1) ++ ", " ++ show (original r)

{- Old version:
{-
Compare two polynomials in [0, 1).
Precondition: p == q or diffRadical generates the same radical as p - q.
* Nothing: p /= q and one of of: more than one intersection, diffRadical is not the radical of p - q.
* Just (Left v): p and q are comparable; if v, then p <= q, else p >= q.
* Just (Right v):
  - p and q intersect exactly once, at the position given by the unique root of diffRadical in [0, 1),
  - if v, then p < q on the left and p > q on the right, otherwise dually.
-}
comparePoly :: (Ring a, Ord a) => Poly a -> Poly a -> Poly a -> Maybe (Either Bool Bool)
comparePoly p q diffRadical = if
  | d == 0 -> Just $ Left smaller_0
  | d == 1 -> Just $ if
    | evalZero diff == zero -> Left smaller_0
    | smaller_0 == smaller_1 -> Left smaller_0
    | otherwise -> Right smaller_0
  | otherwise -> Nothing
  where
  d = descartes True diffRadical
  diff = p - q
  smaller_0 = lowestNonzero diff <= zero
  smaller_1 = lowestNonzero (flipPoly diff) <= zero
-}

{-
Compare two polynomials in [0, 1).
Precondition: p == q or diffRadical generates the same radical as p - q.
* Nothing: p /= q and one of of: more than one intersection, diffRadical is not the radical of p - q.
* Just (Left v): p and q are comparable; if v, then p <= q, else p >= q.
* Just (Right (v_0, v_1)):
  - p and q intersect exactly once in [0, 1), at the position given by the unique root of diffRadical in [0, 1),
  - v_0 /= v_1,
  - on the left/right of the intersection: if v_{0/1} then p < q else p > q.
-}
comparePoly :: (Show a, Ring a, Ord a) => Poly a -> Poly a -> Poly a -> Maybe (Either Bool (Square Bool))
comparePoly p q diffRadical = mayTrace ("comparing " ++ show p ++ " and " ++ show q ++ " using " ++ show diffRadical ++ " and " ++ show diff ++ ": " ++ show r) r
  where
  d = descartes True diffRadical
  diff = p - q
  diff_neg_0 = scaleInput (negate one) diff
  diff_neg_1 = translateInput (negate one) diff_neg_0
  smaller_0 = lowestNonzero diff_neg_0 <= zero
  smaller_1 = lowestNonzero diff_neg_1 <= zero
  r = if
    | d == 0 -> Just $ Left $ evalZero diff <= zero
    | d == 1 -> Just $ if smaller_0 == smaller_1
      then Left smaller_0
      else Right (smaller_0, smaller_1)
    | otherwise -> Nothing

comparePoly' :: (Show a, Ring a, Ord a) => ZoomedPoly a -> ZoomedPoly a -> ZoomedApproxPoly a -> Maybe (Either Bool (Square Bool))
comparePoly' p q diffRadical = comparePoly (zoomed p) (zoomed q) (zoomed $ viewApprox diffRadical)

minP :: (Show a, Field a, Ord a) => ZoomData a -> ZoomedPoly a -> ZoomedPoly a -> ZoomedApproxPoly a -> PiecewisePoly a
minP z p q pq = mayTrace ("minP: " ++ show z ++ "\n* p: " ++ show p ++ "\n* q: " ++ show q ++ "\n* pq: " ++ show pq) $ case comparePoly' p q pq of
  Nothing -> deepen
  Just (Left v) -> PWPoly $ if v then p else q
  Just (Right vs) -> normalizedIntersect (viewApprox pq, tabulateBool $ \i -> if lookupBool vs i then p else q)
  where
  deepen = normalizedBisect' z $ \i -> let
    b :: (Field a, Zoomable a x) => x -> x
    b = bisected' i
    in minP (b z) (b p) (b q) (b pq)

minP' :: (Show a, Field a, Ord a) => ZoomData a -> ZoomedPoly a -> ZoomedPoly a -> Maybe (ZoomedApproxPoly a) -> PiecewisePoly a
minP' z p q pq' = minP z p q pq where
  pq = flip fromMaybe pq' $ radicalApprox $ p - q

minPI :: (Show a, Field a, Ord a) => ZoomData a -> ZoomedPoly a -> Intersect a -> Square (ZoomedApproxPoly a) -> ZoomedApproxPoly a -> PiecewisePoly a
minPI z p q@(s, qs@(q_0, q_1)) pq@(pq_0, pq_1) common = mayTrace ("minPI:\n* z: " ++ show z ++ "\n* p: " ++ show p ++ "\n* q_0: " ++ show q_0 ++ "\n* q_1: " ++ show q_1 ++ "\n* s: " ++ show s ++ "\n* pq_0: " ++ show pq_0 ++ "\n* pq_1: " ++ show pq_1 ++ "\n* common: " ++ show common) res where
  res = case comparePoly' p q_0 pq_0 of
    Nothing -> mayTrace "Nothing on left" deepen
    Just (Left True) -> minP z p q_1 pq_1  -- TODO: could continue with a specialized version of minPI.
    Just (Left False) -> PWIntersect q
    Just (Right (v_0, _)) -> case comparePoly' p q_1 pq_1 of
      Nothing -> mayTrace "Nothing on right" deepen
      Just (Left True) -> minP z p q_0 pq_0  -- TODO: could continue with a specialized version of minPI.
      Just (Left False) -> PWIntersect q
      Just (Right (_, v_1)) ->
        {-
        Now we know that p has exactly one intersection with each of q_0 and q_1.
        If they are different intersections, we deepen.
        If the are the same, we have a direct result using v_0 and v_1.
        -}
        if degree (zoomed $ viewApprox common) == 0
        then mayTrace "exactly one intersection each, but no common" deepen
        -- TODO: regenerate intersection polynomial if p is involved (for reproducibility).
        else normalizedIntersect (s, tabulateBool $ \i -> if lookupBool (v_0, v_1) i then p else lookupBool qs i)
    where
    deepen = normalizedBisect' z $ \i -> let
      b :: (Field a, Zoomable a x) => x -> x
      b = bisected' i
      in case lookupBool qs i of
        PWPoly q' -> minP (b z) (b p) q' (b $ lookupBool pq i)
        PWIntersect q' -> minPI (b z) (b p) q' (tabulateBool $ b . lookupBool pq) (b common)
      where
      qs = bisectedIntersect q

  -- Tracing stuff.
  c = approxTrueOrig common
  a0 = approxTrueOrig pq_0
  a1 = approxTrueOrig pq_1
  d = radical $ gcdP a0 a1
  e = radical $ gcdP (radical $ original p - original q_0) (radical $ original p - original q_1)
  res' | not $ approxTrueOrig pq_0 == radical (original p - original q_0) = error $ "minPI: mismatch in pq_0 " ++ show (approxTrueOrig pq_0) ++ " vs. " ++ show (radical (original p - original q_0))
       | not $ approxTrueOrig pq_1 == radical (original p - original q_1) = error $ "minPI: mismatch in pq_1 " ++ show (approxTrueOrig pq_1) ++ " vs. " ++ show (radical (original p - original q_1))
       | not $ similar (c, d) = error $ "minPI: common mismatch " ++ show c ++ " vs. " ++ show d ++ " vs. " ++ show e
       -- | p - q_0 `elem` [viewApprox pq_0, negate $ viewApprox pq_0] && p - q_1 `elem` [viewApprox pq_1, negate $ viewApprox pq_1] = res
       | otherwise = res

minPI' :: (Show a, Field a, Ord a) => ZoomData a -> ZoomedPoly a -> Intersect a -> Square (Maybe (ZoomedApproxPoly a)) -> Maybe (ZoomedApproxPoly a) -> PiecewisePoly a
minPI' z p q@(_, qs) pq' common' = mayTrace ("minPI': " ++ show pq' ++ ", " ++ show common') $ minPI z p q pq common where
  pq = tabulateBool $ \i -> flip fromMaybe (lookupBool pq' i) $ radicalApprox $ p - lookupBool qs i
  common = flip fromMaybe common' $ radicalGCDApprox $ fmap (\i -> p - lookupBool qs i) [True, False]  -- TODO: reuse radical calculations from above? Probably not worth it.

minII :: (Show a, Field a, Ord a) => ZoomData a -> Intersect a -> Intersect a -> Square (ZoomedApproxPoly a) -> ZoomedApproxPoly a -> PiecewisePoly a
minII z p@(r, ps@(p_0, p_1)) q@(s, qs@(q_0, q_1)) pq@(pq_0, pq_1) common = mayTrace ("minII:\n* z: " ++ show z ++ "\n* p_0: " ++ show p_0 ++ "\n* p_1: " ++ show p_1 ++ "\n* r: " ++ show r ++ "\n* q_0: " ++ show q_0 ++ "\n* q_1: " ++ show q_1 ++ "\n* s: " ++ show s ++ "\n* pq_0: " ++ show pq_0 ++ "\n* pq_1: " ++ show pq_1 ++ "\n* common: " ++ show common) res
  where
  res = case comparePoly' p_0 q_0 pq_0 of
    Nothing -> deepen
    Just (Left v) -> minPI' z (if v then q_1 else p_1) (if v then p else q) (Nothing, Just pq_1) Nothing  -- TODO: could continue with a specialized version of minII.
    Just (Right (v_0, _)) -> case comparePoly' p_1 q_1 pq_1 of
      Nothing -> deepen
      Just (Left v) -> minPI' z (if v then q_0 else p_0) (if v then p else q) (Just pq_0, Nothing) Nothing  -- TODO: could continue with a specialized version of minII.
      Just (Right (_, v_1)) ->
        {-
        Now we know that p_i has exactly one intersection with q_i.
        If they are different intersections, we deepen.
        If the are the same, we have a direct result using v_0 and v_1.
        -}
        if degree (zoomed $ viewApprox common) == 0
        then deepen
        -- TODO: regenerate intersection polynomial if necessary (for reproducibility).
        else normalizedIntersect (s, tabulateBool $ \i -> if lookupBool (v_0, v_1) i then lookupBool ps i else lookupBool qs i)
    where
    deepen = normalizedBisect' z $ \i -> let
      b :: (Field a, Zoomable a x) => x -> x
      b = bisected' i
      mixed p' q'@(_, qs') = minPI' (b z) p' q' (tabulateBool $ \j -> do {guard False; guard $ j == i; return $ b $ lookupBool pq j}) Nothing --(Just $ bisected' i common)
      in case (lookupBool ps i, lookupBool qs i) of
        (PWPoly p', PWPoly q') -> minP (b z) p' q' (b $ lookupBool pq i)
        (PWIntersect p', PWIntersect q') -> minII (b z) p' q' (tabulateBool $ b . lookupBool pq) (bisected' i common)
        (PWPoly p', PWIntersect q'@(_, qs')) -> mixed p' q'
        (PWIntersect p'@(_, ps'), PWPoly q') -> mixed q' p'
      where
      ps = bisectedIntersect p
      qs = bisectedIntersect q

  -- Tracing stuff.
  c = approxTrueOrig common
  a0 = approxTrueOrig pq_0
  a1 = approxTrueOrig pq_1
  d = radical $ gcdP a0 a1
  e = radical $ gcdP (radical $ original p_0 - original q_0) (radical $ original p_1 - original q_1)
  res' | not $ approxTrueOrig pq_0 == radical (original p_0 - original q_0) = error $ "minII: mismatch in pq_0 " ++ show (approxTrueOrig pq_0) ++ " vs. " ++ show (radical (original p_0 - original q_0))
       | not $ approxTrueOrig pq_1 == radical (original p_1 - original q_1) = error $ "minII: mismatch in pq_1 " ++ show (approxTrueOrig pq_1) ++ " vs. " ++ show (radical (original p_1 - original q_1))
       | not $ similar (c, d) = error $ "minII: common mismatch " ++ show c ++ " vs. " ++ show d ++ " vs. " ++ show e
       -- | p_0 - q_0 `elem` [viewApprox pq_0, negate $ viewApprox pq_0] && p_1 - q_1 `elem` [viewApprox pq_1, negate $ viewApprox pq_1] = res
       | otherwise = res
  
minII' :: (Show a, Field a, Ord a) => ZoomData a -> Intersect a -> Intersect a -> Square (Maybe (ZoomedApproxPoly a)) -> Maybe (ZoomedApproxPoly a) -> PiecewisePoly a
minII' z p@(_, ps) q@(_, qs) pq' common' = minII z p q pq common where
  pq = tabulateBool $ \i -> flip fromMaybe (lookupBool pq' i) $ radicalApprox $ lookupBool ps i - lookupBool qs i
  common = flip fromMaybe common' $ radicalGCDApprox $ fmap (\i -> lookupBool ps i - lookupBool qs i) [True, False]  -- TODO: reuse radical calculation from above? Probably not worth it.

minPW' :: (Show a, Field a, Ord a) => ZoomData a -> Square (PiecewisePoly a) -> PiecewisePoly a
minPW' z (u, v) = case (u, v) of
  (PWPoly p, PWPoly q) -> minP' z p q Nothing
  (PWPoly p, PWIntersect q) -> minPI' z p q (Nothing, Nothing) Nothing
  (PWIntersect p, PWPoly q) -> minPI' z q p (Nothing, Nothing) Nothing
  (PWIntersect p, PWIntersect q) -> minII' z q p (Nothing, Nothing) Nothing
  _ -> deepen
  where
  us = bisectedPW u
  vs = bisectedPW v
  deepen = normalizedBisect' z $ \i -> minPW' (bisected' i z) (lookupBool us i, lookupBool vs i)

-- Assumes that each polynomial piece is minimal on its domain with respect to all the pieces.
-- This makes for a more efficient implementation of minII.
-- But we could also make it work in general.
-- Then the construction becomes more generic, closer to piecewiseBinOp.
-- TODO: Measure impact.
minPW :: Square (PiecewisePoly Rational) -> PiecewisePoly Rational
minPW (p, q) = shouldTrace ("minPW\n" ++ showPW p ++ showPW q) $ shouldTrace ("minPW result:\n" ++ showPW r) r where
  r = minPW' mempty (p, q)
  r' = case testMinPW 128 [p, q] r of
    Just () -> r
    Nothing -> mayTrace ("minPW broken here:\n" ++ showPW p ++ showPW q) $ error ":("

--minPWs :: (Show a, Field a, Ord a) => [PiecewisePoly a] -> PiecewisePoly a
minPWs = foldr1 $ curry minPW

piecewiseBinOp :: (Show a, Field a, Ord a) => Bool -> (Square (Poly a) -> Poly a) -> Square (PiecewisePoly a) -> PiecewisePoly a
piecewiseBinOp regen op = h mempty where
  opRegen z = (original *** original) >>> op >>> zoomedGenerate z
  opNotRegen _ = uncurry (liftA2 (,)) >>> fmap op
  op' = if regen then opRegen else opNotRegen
  
  h z (u, v) = case (u, v) of
    (PWPoly p, PWPoly q) -> PWPoly $ op' z (p, q)
    (PWPoly p, PWIntersect (s, (q_0, q_1))) -> PWIntersect (s, (op' z (p, q_0), op' z (p, q_1)))
    (PWIntersect (r, (p_0, p_1)), PWPoly q) -> PWIntersect (r, (op' z (p_0, q), op' z (p_1, q)))
    (PWIntersect (r, (p_0, p_1)), PWIntersect (s, (q_0, q_1))) ->
      if degree (zoomed $ viewApprox $ gcdApprox [r, s]) == 0
      then deepen
      -- TODO:
      -- Whoose between r and s based on size of coefficients?
      -- We could also take their gcd, but that suffers from coefficient blow-up.
      else PWIntersect (r, (op' z (p_0, q_0), op' z (p_1, q_1)))
    _ -> deepen
    where
    us = bisectedPW u
    vs = bisectedPW v
    deepen = normalizedBisect' z $ \i -> h (bisected' i z) (lookupBool us i, lookupBool vs i)

instance (Show a, Ord a, Field a) => Additive (PiecewisePoly a) where
  zero = piecewiseFromPoly zero
  (+) = curry $ piecewiseBinOp False $ uncurry (+)

instance (Show a, Ord a, Field a) => AddGroup (PiecewisePoly a) where
  negate = fmap negate

-- Needed because our piecewise polynomials keep track of what's happening left of an intersection at zero.
-- Multiplying with mempty (the identity) makes it so that the left piece becomes larger than the right piece on the left.
fixZero :: (Show a, Field a, Ord a) => PiecewisePoly a -> PiecewisePoly a
fixZero p = case p of
  PWPoly p -> PWPoly p
  PWIntersect (r, (p_0, p_1)) -> if evalP (zoomed r) zero == zero
    then PWPoly p_1
    else PWIntersect (r, (p_0, p_1))
  PWBisect (p_0, p_1) -> PWBisect (fixZero p_0, p_1)

instance (Show a, Ord a, Field a) => Multiplicative (PiecewisePoly a) where
  one = piecewiseFromPoly one
  (*) = curry $ (fixZero .) $ piecewiseBinOp True $ uncurry (*)

instance (Show a, Field a, Ord a) => Semigroup (PiecewisePoly a) where
  (<>) = curry $ piecewiseBinOp True $ uncurry (<>)

instance (Show a, Field a, Ord a) => Monoid (PiecewisePoly a) where
  mempty = piecewiseFromPoly mempty

integralizePWLinear :: [Either (Poly Rational) (Poly Rational, Square Rational)] -> [Either (Either (Poly Integer) (Poly Rational)) (Poly Integer, Square Rational)]
integralizePWLinear = fmap (bimap f g) where
  f :: Poly Rational -> Either (Poly Integer) (Poly Rational)
  f x | (s, _) <- makeIntegral x, Prelude.abs s == 1 = Left $ fmap numerator x
      | otherwise = Right x

  g :: (Poly Rational, Square Rational) -> (Poly Integer, Square Rational)
  g = first $ makeIntegral >>> snd

showPWLinearIntegral :: [Either (Either (Poly Integer) (Poly Rational)) (Poly Integer, Square Rational)] -> String
showPWLinearIntegral = fmap (either f g >>> ("* " ++)) >>> ("piecewise polynomial in [0, 1]:" :) >>> unlines where
  f :: Either (Poly Integer) (Poly Rational) -> String
  f p = "piece " ++ s p where
    s (Left p) = show (unP p)
    s (Right p) = show (unP p)

  g :: (Poly Integer, Square Rational) -> String
  g (r, (b_0, b_1)) = "separated by root of " ++ show (unP r) ++ " between " ++ show b_0 ++ " and " ++ show b_1

showPW :: PiecewisePoly Rational -> String
showPW = linearizePW >>> integralizePWLinear >>> showPWLinearIntegral

printPW :: PiecewisePoly Rational -> IO ()
printPW = showPW >>> putStrLn

--testMinPW :: (Show a, Field a, Ord a) => Integer -> [PiecewisePoly a] -> PiecewisePoly a -> Maybe ()
testMinPW :: Integer -> [PiecewisePoly Rational] -> PiecewisePoly Rational -> Maybe ()
testMinPW n ps q = mayTrace ("testMinPW:\n" ++ showPW q ++ concat (fmap showPW ps)) $ forM_ [0..n-1] $ \k -> do
  let x = k % n
  let m = minimum (fmap (`evalPW` x) ps)
  let m' = evalPW q x
  if m' == m
    then return ()
    else mayTrace ("problem at " ++ show x ++ ": " ++ show m' ++ " vs. actual " ++ show m) Nothing

-- -[a^2 X^2 + (1 - a)^2 (1 - X)] for a in [0, 1].
-- This family of polynomials has minimum given by two pieces (given by a in {0, 1}).
s :: Rational -> Poly Rational
s a = negate $ square a' * mempty + square (one - a') * (one - mempty) where
  a' = scalar a

{-
Piecewise polynomial in [0, 1]:
* piece [-1,1]
* separated by root of [-1,2] between 0 % 1 and 1 % 1
* piece [0,-1]
-}
s' :: PiecewisePoly Rational
s' = [0 .. depth] & map ((% depth) >>> s >>> piecewiseFromPoly) & minPWs where
  depth = 100

-- [(a X)^2 + ((1 - a) (1 - X))^2] for a in [0, 1].
-- This family of polynomials has minimum given by 2 (X (1 - X))^2.
t :: Rational -> Poly Rational
t a = square (a' * mempty) + square ((one - a') * (one - mempty)) where
  a' = scalar a

-- Here a ranges only over a finite subsets of [0, 1].
-- The piecewise polynomial approximation consists of one piece for every a.
t' :: PiecewisePoly Rational
t' = [0 .. depth] & map ((% depth) >>> t >>> piecewiseFromPoly) & minPWs where
  depth = 100

main :: IO ()
main = do
  printPW s'
  printPW t'
