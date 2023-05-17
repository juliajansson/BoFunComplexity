{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE RankNTypes #-}
module PiecewisePoly where

import Control.Applicative (Applicative(..))
import Control.Arrow ((>>>))
import Control.Monad (forM_, guard)
import Data.Bifunctor (Bifunctor(..), bimap)
import Data.Function ((&))
import Data.Maybe (fromMaybe, fromJust, isJust)
import Data.Ratio ((%), numerator)
import qualified Data.Set as S (Set, fromList, size)
import Debug.Trace (trace, traceShow)
import Prelude hiding (Num(..),Fractional(..), fromIntegral, min, sum, product)
import qualified Prelude

import DSLsofMath.Algebra
import DSLsofMath.PSDS (Poly(P,unP), evalP, degree, comP, gcdP)

import Util
import PolynomialExtra


-- | Zoom data:
-- Affine transformations stratified into levels.
-- The intended use case is iterated reparametrizations of halves of the unit interval (and possibly their inverses).
-- Here, the scale is two to the power of the negated zoom level.
data ZoomData a = ZoomData {
  zoomLevel :: Int,               -- ^ TODO: decide if we want that here
  zoomAffinePoly :: AffinePoly a  -- ^ affine transformation
} deriving (Eq, Ord, Show, Read, Functor)

instance (Ring a) => Semigroup (ZoomData a) where
  ZoomData l0 a0 <> ZoomData l1 a1 = ZoomData (l0 + l1) (a0 <> a1)

instance (Ring a) => Monoid (ZoomData a) where
  mempty = ZoomData 0 (affineFromPoly mempty)

instance (Field a) => Group (ZoomData a) where
  invert (ZoomData l a) = ZoomData (-l) (invert a)

zoomEval :: (Ring a) => ZoomData a -> a -> a
zoomEval = zoomAffinePoly >>> affinePoly >>> evalP


-- | TODO: memoize
zoomHalf :: (Field a) => Bool -> ZoomData a
zoomHalf bp = ZoomData 1 $ AffinePoly (one / two) $ if bp then zero else one / two

zoomLeft :: (Field a) => ZoomData a
zoomLeft = zoomHalf True

zoomRight :: (Field a) => ZoomData a
zoomRight = zoomHalf False


-- | Right zoom algebras.
class Ring a => Zoomable a x | x -> a where
  zoom :: ZoomData a -> x -> x

-- Just Haskell stuff: can't give zoomable instance for unit type.
-- Also, this seems to conflict with other instances.
--instance (Zoomable a x, Zoomable b x) => Zoomable (a, b) x where
--  zoom z (a, b) = (zoom z a, zoom z b)

-- | Yoneda embedding.
instance (Ring a) => Zoomable a (ZoomData a) where
  zoom z z' = z' <> z

-- | TODO: why is UndecidableInstances needed here?
instance (Ring a) => Zoomable a (Poly a) where
  zoom (ZoomData _ t) = (`comP` affinePoly t)


-- | The graph of the counit map of free Zoom algebra adjunction.
data Zoomed a x = Zoomed
  { original :: x           -- ^ the data at original scale
  , zoomData :: ZoomData a  -- ^ the zoom
  , zoomed :: x             -- ^ the zoomed data
  } deriving (Show, Read)

instance Functor (Zoomed a) where
  fmap f (Zoomed original z zoomed) = Zoomed (f original) z (f zoomed)

instance Bifunctor Zoomed where
  bimap f g (Zoomed original z zoomed) = Zoomed (g original) (f <$> z) (g zoomed)

-- | Really this is an instance of Applicative for each fixed zoomData attribute.
instance Applicative (Zoomed a) where
  pure x = Zoomed x (error "pure for Zoomed lacks zoomData attribute") x
  Zoomed fOrig z fZoomed <*> Zoomed xOrig _ xZoomed = Zoomed (fOrig xOrig) z (fZoomed xZoomed) 

-- | Zoomed a is a pointed functor.
zoomedTrivial :: (Ring a) => x -> Zoomed a x
zoomedTrivial v = Zoomed v mempty v

zoomedGenerate :: (Zoomable a x) => ZoomData a -> x -> Zoomed a x
zoomedGenerate z v = Zoomed v z $ zoom z v

zoomedRegenerate :: (Zoomable a x) => ZoomData a -> Zoomed a x -> Zoomed a x
zoomedRegenerate z = original >>> zoomedGenerate z

instance (Zoomable a x) => Zoomable a (Zoomed a x) where
  zoom z (Zoomed original z' zoomed) = Zoomed original (zoom z z') (zoom z zoomed)

-- | Requirement: zooming preserves the additive structure.
class (Zoomable a x, AddGroup x) => ZoomableAddGroup a x

instance (Ring a) => ZoomableAddGroup a (Poly a)

-- | These are really instances fibred over a given zoom data.
instance (ZoomableAddGroup x a) => Additive (Zoomed x a) where
  zero = error "zero for Zoomed not really available"
  Zoomed o0 d z0 + Zoomed o1 _ z1 = Zoomed o d z where
    o = o0 + o1
    z = z0 + z1

instance (ZoomableAddGroup x a) => AddGroup (Zoomed x a) where
  negate (Zoomed o d z) = Zoomed (negate o) d (neg z)


-- | Approximations to values that turn into the exact values below a given zoom level.
data ZoomedApprox a x = ZoomedApprox {
  approxValue :: Zoomed a x,     -- ^ current value
  approxInfo  :: Maybe (Int, x)  -- ^ if current value is approximation: 
                                 -- level bound below it is to be used
                                 -- and actual value
} deriving (Show, Read)

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
  fmap f (ZoomedApprox value m) = ZoomedApprox (f <$> value) (fmap f <$> m)

-- | There are two evident Zoomable instances.
-- The functorial one that doesn't normalize and the one given here.
instance (Show a, Show x, Zoomable a x) => Zoomable a (ZoomedApprox a x) where
  zoom z (ZoomedApprox value m) = normalizeApprox $ ZoomedApprox (zoom z value) m


type ZoomedPoly a = Zoomed a (Poly a)
type ZoomedApproxPoly a = ZoomedApprox a (Poly a)

radicalApprox :: (Show a, Field a, Ord a) => ZoomedPoly a -> ZoomedApproxPoly a
radicalApprox v@(Zoomed p _ _) = normalizeApprox $ ZoomedApprox v $ Just (5 + degree p, radical p)

gcdApprox :: (Field a, Ord a) => [ZoomedPoly a] -> ZoomedApproxPoly a
gcdApprox xs  =  normalizeApprox
              $  ZoomedApprox (zoomedGenerate (zoomData (head xs)) one)
              $  Just (3 + (sum (map degree ps) `div` length xs), gcdMany ps)
  where
  ps = map original xs

radicalGCDApprox :: (Show a, Field a, Ord a) => [ZoomedPoly a] -> ZoomedApproxPoly a
radicalGCDApprox xs  =  normalizeApprox
                     $  ZoomedApprox (zoomedGenerate (zoomData (head xs)) one)
                     $  Just (3 + (sum (map degree ps) `div` length xs), radical $ gcdMany ps)
  where
  ps = map original xs


bisected' :: (Field a, Zoomable a x) => Bool -> x -> x
bisected' = zoom . zoomHalf

bisected :: (Field a, Zoomable a x) => x -> (x, x)
bisected = tabulateBool . flip bisected'


-- | A tuple (r, (p_0, p_1)) denotes a two-piece polynomial in [0, 1] (zoomed).
-- The switch from the left piece p_0 to the right piece p_1 is given
-- by the unique root of r in (0, 1).
type Intersect a = (ZoomedPoly a, Square (ZoomedPoly a))

-- | Checks if the separating polynomial has a unique root in the expected.
checkIntersect :: (Show a, Ring a, Ord a) => Intersect a -> Maybe ()
checkIntersect (r, (p_0, p_1)) = case comparePoly (zoomed p_0, zoomed p_1) (zoomed r) of
  Just (Right _) -> Just ()
  _ -> Nothing

-- | Regenerate an intersect at a specified zoom level.
-- Returns Nothing if the resulting intersect is invalid.
intersectRegenerate :: (Show a, Ring a, Ord a) => ZoomData a -> Intersect a -> Maybe (Intersect a)
intersectRegenerate z (r, p) = intersect <$ checkIntersect intersect where
  intersect = (zoomedRegenerate z r, tabulateBool $ lookupBool p >>> zoomedRegenerate z)

{-|
A piecewise polynomial at some zoom level.
The domain of definition is rescaled to [0, 1).

PWBisect right composes current zoom according to 'bisected'.

Switches between pieces are captured:
* at dyadic numbers by PWBisect,
* at other algebaic numbers by PWIntersect.
-}
data PiecewisePoly a =
    PWPoly (ZoomedPoly a)
  | PWIntersect (Intersect a)
  | PWBisect (Square (PiecewisePoly a))
  deriving (Show)

instance Functor PiecewisePoly where fmap = fmapPW

fmapPW :: (a->b) -> PiecewisePoly a -> PiecewisePoly b
fmapPW f p = let f' = bimap f (fmap f) in  case p of
    PWPoly p             -> PWPoly $ f' p
    PWIntersect (r, ps)  -> PWIntersect (f' r, tabulateBool $ lookupBool ps >>> f')
    PWBisect ps          -> PWBisect $ tabulateBool $ lookupBool ps >>> fmap f

pwCheckZoomData :: (Field a, Eq a) => ZoomData a -> PiecewisePoly a -> Maybe ()
pwCheckZoomData z p = let check p = guard $ zoomData p == z in case p of
  PWPoly p                     ->  check p
  PWIntersect (r, (p_0, p_1))  ->  forM_ [r, p_0, p_1] check
  PWBisect p                   ->  forM_ [True, False] $ \i ->
                                     pwCheckZoomData (bisected' i z) (lookupBool p i)

isPoly :: PiecewisePoly a -> Bool
isPoly (PWPoly _) = True
isPoly _ = False

piecewiseFromPoly :: (Ring a) => Poly a -> PiecewisePoly a
piecewiseFromPoly = zoomedTrivial >>> PWPoly

data Separation' a a' = Dyadic a | Algebraic (Poly a', (a, a))
  deriving (Eq, Ord)

type Separation a = Separation' a a

linearizePW' :: (Eq a, Field a) =>
    ZoomData a -> PiecewisePoly a -> [Either (Poly a) (Separation a)]
linearizePW' z p = case p of
  PWBisect p -> onBisect p
  _ -> onOther
  where
  onBisect p = h $ case unify (p_0, p_1) of
    Just p   ->  [Left p]
    Nothing  ->  [Left p_0, Right $ Dyadic $ fromJust $ unify (s_0, s_1), Left p_1]
    where
    xs@(x_0, x_1) = tabulateBool $ \i -> linearizePW' (bisected' i z) (lookupBool p i)
    Right (Dyadic s_0) : Left p_0 : y_0 = reverse x_0
    Right (Dyadic s_1) : Left p_1 : y_1 = x_1
    h u = reverse y_0 ++ u ++ y_1

  onOther = h $ case p of
    PWPoly p -> [Left $ original p]
    PWIntersect (r, p) -> let
      (p_0, p_1) = mapPair original p in
      [Left p_0, Right $ Algebraic (original r, b), Left p_1]
    where
    b = tabulateBool $ lookupBool (zero, one) >>> zoomEval z
    (b_0', b_1') = tabulateBool $ lookupBool b >>> Dyadic >>> Right
    h u = [b_0'] ++ u ++ [b_1']

-- TODO: Find better return type.
linearizePW :: (Field a, Eq a) => PiecewisePoly a -> [Either (Poly a) (Separation a)]
linearizePW = linearizePW' mempty

bisectedIntersect :: (Field a, Ord a) => Intersect a -> Square (PiecewisePoly a)
bisectedIntersect (r, (p_0, p_1)) = if
  | squarefreeRoot $ zoomed r_l -> (PWIntersect (r_l, (p_0_l, p_1_l)), PWPoly p_1_r)
  | squarefreeRoot $ zoomed r_r -> (PWPoly p_0_l, PWIntersect (r_r, (p_0_r, p_1_r)))
  | otherwise -> (PWPoly p_0_l, PWPoly p_1_r)
  where
  (r_l, r_r) = bisected r
  (p_0_l, p_0_r) = bisected p_0
  (p_1_l, p_1_r) = bisected p_1

bisectedPW :: (Field a, Ord a) => PiecewisePoly a -> Square (PiecewisePoly a)
bisectedPW (PWBisect x)     =  x
bisectedPW (PWPoly p)       =  mapPair PWPoly $ bisected p
bisectedPW (PWIntersect x)  =  bisectedIntersect x

evalPW' :: (Field a, Ord a) => ZoomData a -> PiecewisePoly a -> a -> a
evalPW' z p x = case p of
  PWPoly p -> evalP (original p) x
  PWIntersect (r, ps) -> if evalP (original r) x == zero
    then fromJust $ unify $ tabulateBool $ lookupBool ps >>> ev
    else deepen
  PWBisect p -> deepen
  where
  ev p = evalP (original p) x
  s = invert >>> zoomAffinePoly >>> affinePoly >>> (`evalP` x)
  i = s (zoom zoomLeft z) < one
  deepen = evalPW' (bisected' i z) (lookupBool (bisectedPW p) i) x

evalPW :: (Field a, Ord a) => PiecewisePoly a -> a -> a
evalPW = evalPW' mempty

normalizedBisect :: (Show a, Ring a, Ord a) =>
    ZoomData a -> Square (PiecewisePoly a) -> PiecewisePoly a
normalizedBisect z p = case p of
  (PWPoly p_0, PWPoly p_1) -> h (p_0, p_1) $ return $ PWPoly $ zoomedRegenerate z p_0
  (PWPoly p_0, PWIntersect p_1@(_, (p_10, _))) -> h (p_0, p_10) $ PWIntersect <$> intersectRegenerate z p_1
  (PWIntersect p_0@(_, (_, p_01)), PWPoly p_1) -> h (p_1, p_01) $ PWIntersect <$> intersectRegenerate z p_0
  _ -> def
  where
  def = PWBisect p
  h p f = fromMaybe def $ do
    unify $ mapPair original p
    f

normalizedBisect' :: (Show a, Field a, Ord a) =>
    ZoomData a -> (Bool -> PiecewisePoly a) -> PiecewisePoly a
normalizedBisect' z = tabulateBool >>> normalizedBisect z

normalizedIntersect :: (Show a, Ring a, Eq a) => Intersect a -> PiecewisePoly a
normalizedIntersect p@(r, (p_0, p_1)) = res where
  res = if original p_0 == original p_1
    then PWPoly p_0
    else PWIntersect p
  res' | original p_0 - original p_1 `elem` [original r, negate $ original r] = res
       | otherwise = error $ "THE STRANGEST THING: " ++ show (original p_0) ++ ", "
                                                     ++ show (original p_1) ++ ", "
                                                     ++ show (original r)

{-|
Compare two polynomials in (0, 1).
Precondition: p == q or diffRadical generates the same radical as p - q.
* Nothing: p /= q and one of: more than one intersection, diffRadical is not the radical of p - q.
* Just (Left v): p and q are comparable; if v, then p <= q, else p >= q.
* Just (Right (v_0, v_1)):
  - p and q intersect exactly once in (0, 1), at the position given by the unique root of diffRadical in that interval,
  - v_0 /= v_1,
  - on the left/right of the intersection: if v_{0/1} then p < q else p > q.
-}
comparePoly :: (Show a, Ring a, Ord a) =>
    Square (Poly a) -> Poly a -> Maybe (Either Bool (Square Bool))
comparePoly (p, q) diffRadical = case descartesUnitInterval True diffRadical of
  Nothing  ->  Just $ Left True
  Just 0   ->  Just $ Left smaller_0
  Just 1   ->  Just $ if smaller_0 == smaller_1
                      then  Left smaller_0
                      else  Right (smaller_0, smaller_1)
  _        ->  Nothing
  where
  diff = p - q
  check p = lowestNonzero p <= zero
  smaller_0 = check diff
  smaller_1 = check $ flipUnitIntervalPoly diff

comparePoly' :: (Show a, Ring a, Ord a) =>
    Square (ZoomedPoly a) -> ZoomedApproxPoly a -> Maybe (Either Bool (Square Bool))
comparePoly' ps diffRadical = comparePoly (mapPair zoomed ps) (zoomed $ viewApprox diffRadical)

minP :: (Show a, Field a, Ord a) =>
    ZoomData a -> ZoomedPoly a -> ZoomedPoly a -> ZoomedApproxPoly a -> PiecewisePoly a
minP z p q pq = case comparePoly' (p, q) pq of
  Nothing -> deepen
  Just (Left v) -> PWPoly $ if v then p else q
  Just (Right vs) -> normalizedIntersect (viewApprox pq, tabulateBool $ \i -> if lookupBool vs i then p else q)
  where
  deepen = normalizedBisect' z $ \i -> let
    b :: (Field a, Zoomable a x) => x -> x
    b = bisected' i
    in minP (b z) (b p) (b q) (b pq)

minP' :: (Show a, Field a, Ord a) =>
    ZoomData a -> ZoomedPoly a -> ZoomedPoly a -> Maybe (ZoomedApproxPoly a) -> PiecewisePoly a
minP' z p q pq' = minP z p q pq where
  pq = flip fromMaybe pq' $ radicalApprox $ p - q

minPI :: (Show a, Field a, Ord a) =>
    ZoomData a -> ZoomedPoly a -> Intersect a ->
    Square (ZoomedApproxPoly a) -> ZoomedApproxPoly a -> PiecewisePoly a
minPI z p q@(s, qs@(q_0, q_1)) pq@(pq_0, pq_1) common = case comparePoly' (p, q_0) pq_0 of
    Nothing -> deepen
    Just (Left True) -> minP z p q_1 pq_1  -- TODO: could continue with a specialized version of minPI.
    Just (Left False) -> PWIntersect q
    Just (Right (v_0, _)) -> case comparePoly' (p, q_1) pq_1 of
      Nothing -> deepen
      Just (Left True) -> minP z p q_0 pq_0  -- TODO: could continue with a specialized version of minPI.
      Just (Left False) -> PWIntersect q
      Just (Right (_, v_1)) ->
        {-
        Now we know that p has exactly one intersection with each of q_0 and q_1.
        If they are different intersections, we deepen.
        If the are the same, we have a direct result using v_0 and v_1.
        -}
        if degree (zoomed $ viewApprox common) == 0
        then deepen
        -- TODO: regenerate intersection polynomial if p is involved (for reproducibility).
        else normalizedIntersect (s, tabulateBool $ \i -> if lookupBool (v_0, v_1) i then p else lookupBool qs i)
    where
    deepen = normalizedBisect' z $ \i -> let
      b :: (Field a, Zoomable a x) => x -> x
      b = bisected' i
      in case lookupBool qs i of
        PWPoly q'       -> minP   (b z) (b p) q' (b $ lookupBool pq i)
        PWIntersect q'  -> minPI  (b z) (b p) q' (tabulateBool $ b . lookupBool pq) (b common)
      where
      qs = bisectedIntersect q

minPI' :: (Show a, Field a, Ord a) =>
    ZoomData a -> ZoomedPoly a -> Intersect a ->
    Square (Maybe (ZoomedApproxPoly a)) -> Maybe (ZoomedApproxPoly a) -> PiecewisePoly a
minPI' z p q@(_, qs) pq' common' = minPI z p q pq common where
  pq = tabulateBool $ \i -> flip fromMaybe (lookupBool pq' i) $ radicalApprox $ p - lookupBool qs i
  common = flip fromMaybe common' $ radicalGCDApprox $ fmap (\i -> p - lookupBool qs i) [True, False]
    -- ^ TODO: reuse radical calculations from above? Probably not worth it.

minII :: (Show a, Field a, Ord a) =>
    ZoomData a -> Intersect a -> Intersect a ->
    Square (ZoomedApproxPoly a) -> ZoomedApproxPoly a -> PiecewisePoly a
minII z p@(r, ps@(p_0, p_1)) q@(s, qs@(q_0, q_1)) pq@(pq_0, pq_1) common = case comparePoly' (p_0, q_0) pq_0 of
    Nothing -> deepen
    Just (Left v) -> minPI' z (if v then q_1 else p_1) (if v then p else q) (Nothing, Just pq_1) Nothing  -- TODO: could continue with a specialized version of minII.
    Just (Right (v_0, _)) -> case comparePoly' (p_1, q_1) pq_1 of
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
  
minII' :: (Show a, Field a, Ord a) =>
    ZoomData a -> Intersect a -> Intersect a ->
    Square (Maybe (ZoomedApproxPoly a)) -> Maybe (ZoomedApproxPoly a) -> PiecewisePoly a
minII' z p@(_, ps) q@(_, qs) pq' common' = minII z p q pq common where
  pq = tabulateBool $ \i -> flip fromMaybe (lookupBool pq' i) $ radicalApprox $ lookupBool ps i - lookupBool qs i
  common = flip fromMaybe common' $ radicalGCDApprox $ fmap (\i -> lookupBool ps i - lookupBool qs i) [True, False]
    -- ^ TODO: reuse radical calculation from above? Probably not worth it.

minPW' :: (Show a, Field a, Ord a) =>
    ZoomData a -> Square (PiecewisePoly a) -> PiecewisePoly a
minPW' z (u, v) = case (u, v) of
  (PWPoly p,       PWPoly q     )  -> minP'   z p q  Nothing
  (PWPoly p,       PWIntersect q)  -> minPI'  z p q  (Nothing, Nothing) Nothing
  (PWIntersect p,  PWPoly q     )  -> minPI'  z q p  (Nothing, Nothing) Nothing
  (PWIntersect p,  PWIntersect q)  -> minII'  z q p  (Nothing, Nothing) Nothing
  _ -> deepen
  where
  us = bisectedPW u
  vs = bisectedPW v
  deepen = normalizedBisect' z $ \i -> minPW' (bisected' i z) (lookupBool us i, lookupBool vs i)

-- | Assumes that each polynomial piece is minimal on its domain with respect to all the pieces.
-- This makes for a more efficient implementation of minII.
-- But we could also make it work in general.
-- Then the construction becomes more generic, closer to piecewiseBinOp.
-- TODO: Measure impact.
minPW :: (Show a, Field a, Ord a) => Square (PiecewisePoly a) -> PiecewisePoly a
minPW = minPW' mempty

minPWs :: (Show a, Field a, Ord a) => [PiecewisePoly a] -> PiecewisePoly a
minPWs = foldr1 $ curry minPW

piecewiseBinOp :: (Show a, Field a, Ord a) =>
    Bool -> (Square (Poly a) -> Poly a) -> Square (PiecewisePoly a) -> PiecewisePoly a
piecewiseBinOp regen op = h mempty where
  opRegen z = mapPair original >>> op >>> zoomedGenerate z
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
      -- Choose between r and s based on size of coefficients?
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

instance (Show a, Ord a, Field a) => Multiplicative (PiecewisePoly a) where
  one = piecewiseFromPoly one
  (*) = curry $ piecewiseBinOp True $ uncurry (*)

instance (Show a, Field a, Ord a) => Semigroup (PiecewisePoly a) where
  (<>) = curry $ piecewiseBinOp True $ uncurry (<>)

instance (Show a, Field a, Ord a) => Monoid (PiecewisePoly a) where
  mempty = piecewiseFromPoly mempty

integralizePWLinear ::
    [Either (Poly Rational) (Separation Rational)] ->
    [Either  (Either (Poly Integer) (Poly Rational))
             (Separation' Rational Integer)]
integralizePWLinear = fmap (bimap f g) where
  f :: Poly Rational -> Either (Poly Integer) (Poly Rational)
  f x | (s, _) <- makeIntegral x, Prelude.abs s == 1 = Left $ numerator <$> x
      | otherwise = Right x

  g :: Separation Rational -> Separation' Rational Integer
  g (Dyadic x)     = Dyadic x
  g (Algebraic x)  = Algebraic $ first (makeIntegral >>> snd) x

showPWLinearIntegral :: [Either  (Either (Poly Integer) (Poly Rational))
                                 (Separation' Rational Integer)]
                        -> String
showPWLinearIntegral =  fmap (either f g >>> ("+ " ++)) >>>
                        ("piecewise polynomial in [0, 1]:" :) >>>
                        unlines where
  show' :: forall a. (Show a) => Poly a -> String
  show' = unP >>> show

  f :: Either (Poly Integer) (Poly Rational) -> String
  f p = "piece " ++ either show' show' p

  g :: Separation' Rational Integer -> String
  g p = "separated by " ++ s where
    s = case p of
      Dyadic x -> show x
      Algebraic (r, (b_0, b_1))  ->  "root of " ++ show' r
                                 ++  " between " ++ show b_0 ++ " and " ++ show b_1

showPW :: PiecewisePoly Rational -> String
showPW = linearizePW >>> integralizePWLinear >>> showPWLinearIntegral

printPW :: PiecewisePoly Rational -> IO ()
printPW = showPW >>> putStrLn

----------------------------------------------------------------
-- Testing

testMinPW :: (Show a, Field a, Ord a) =>
    Integer -> [PiecewisePoly a] -> PiecewisePoly a -> Maybe ()
testMinPW n ps q = forM_ [0..n] $ \k -> do
  let x = fromRational $ k % n
  let m = minimum $ (`evalPW` x) <$> ps
  let m' = evalPW q x
  if m' == m
    then return ()
    else error $  "testMinPW: problem at "
                ++  show x ++ ": " ++ show m' ++ " vs. actual " ++ show m
             -- ++ "\n" ++  showPW q ++ concatMap showPW ps


-- | -[a^2 X^2 + (1 - a)^2 (1 - X)] for a in [0, 1].
-- This family of polynomials has minimum given by two pieces (given by a in {0, 1}).
s :: Rational -> Poly Rational
s a = negate $ square a' * mempty + square (one - a') * (one - mempty) where
  a' = scalar a

{- |
Piecewise polynomial in [0, 1]:
* piece [-1,1]
* separated by root of [-1,2] between 0 % 1 and 1 % 1
* piece [0,-1]
-}
s' :: PiecewisePoly Rational
s' = [0 .. depth] & map ((% depth) >>> s >>> piecewiseFromPoly) & minPWs where
  depth = 100

-- | [(a X)^2 + ((1 - a) (1 - X))^2] for a in [0, 1].
-- This family of polynomials has minimum given by 2 (X (1 - X))^2.
t :: Rational -> Poly Rational
t a = square (a' * mempty) + square ((one - a') * (one - mempty)) where
  a' = scalar a

-- | Here a ranges only over a finite subsets of [0, 1].
-- The piecewise polynomial approximation consists of one piece for every a.
t' :: PiecewisePoly Rational
t' = [0 .. depth] & map ((% depth) >>> t >>> piecewiseFromPoly) & minPWs where
  depth = 100

main :: IO ()
main = do
  printPW s'
  printPW t'
