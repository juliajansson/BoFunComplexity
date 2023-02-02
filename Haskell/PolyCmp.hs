{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE RebindableSyntax #-}
module PolyCmp (module PolyCmp) where
import qualified Prelude as P
import Prelude hiding (map, Num(..),Fractional(..), fromIntegral, sum, product)
import Data.Ratio ((%))
import qualified Data.Set as S (Set, fromList, size)
import DSLsofMath.Algebra -- (Ring, Field, negate, fromInteger, ifThenElse)
import DSLsofMath.PSDS (Poly(P,unP), evalP, xP, degree, normalPoly, isZero, fromOne,
                        divModP, comP, derP, derL, gcdP, eqPoly, comparePoly,
                        yun)
import Debug.Trace (trace)
----------------
-- Start of (partial) ordering of polynomial by their values in the interval [0,1].

-- Just a synonym to make it easier to change in one place
type OrdField a = (Field a, Ord a, Show a)

{-
Compare two polynomials p1 and p2
  Nothing means "don't know"
  Just ord means that
     forall x. ord ~= compare (p1 x) (p2 x)
-}

cmpPoly :: OrdField a => Poly a -> Poly a -> Maybe Ordering
cmpPoly p1 p2 = cmpZero (normalPoly (p2 - p1))

mayTrace _ = id
--mayTrace = trace

cmpZero :: OrdField a => Poly a -> Maybe Ordering
cmpZero p  | mayTrace ("cmpZero1:"++show r) isZero p = Just EQ
--           | 0==numRoots p =
--             if pmid > zero then Just LT else Just GT -- case 1
           | all even (numRoots' p) = -- case 2
             if       any (zero <) vals  then mayTrace ("cmpZero2LT:"++show r) Just LT
             else if  any (zero >) vals  then mayTrace ("cmpZero2GT:"++show r) Just GT
             else mayTrace ("cmpZero4:"++show r) Nothing -- this should be impossible
           | otherwise = mayTrace ("cmpZero3:"++show r) Nothing
  where  pmid = evalP p (1/2)
         r = length (numRoots' p)  -- the number of distinct roots
         rp2 = fromIntegral (r+2)
         points = [i/rp2 | i <- take (r+1) (iterate (one+) one)]
         vals   = P.map (evalP p) points

{-
case 1: if the polynomial has no roots in (0,1) and at least one point
  (we pick 1/2) is positive, then it is positive everywhere.
  Symmetrically, if some point is negative, it is negative everywhere.
  [The third option, that it would be zero at 1/2, is impossible
  because the polynomial has no roots in (0,1).]  (Note the open
  interval in the first sentence. There may be a root in zero which
  means that we cannot "simplify" the code to just check evalP p 0. I
  tried, and that made some 8-bit subfunctions of |maj2| have over 600
  remaining polynomials, while the correct check with pmid always
  thins to singleton sets! The computation took over 15min and
  returned 3891 polynomials, instead of just one.)

case 2: if p has some roots, but all of them have even multiplicity,
  then the function just "touches" zero at these roots but stays on
  one side otherwise. Earlier we (arbitrarily) picked two points to
  check if it is positive. We could accidentally check at two roots,
  in which case we still didn't know if the function is positive or
  not. To be completely sure we check r+1 points where r = length
  (numRoots' p) is the number of distinct roots. (We have not yet
  encountered a case in any of our computations where this latest step
  is needed.)

-}

-- Now time to make the polynomial sets smaller.

-- there exists a p in ps such that cmpPoly p q = Just Lt, or Le, or Eq
-- If ps cover q it does not need to be added to ps in a union

{-
Test examples (from the partial genPoly maj2 computation)

S.fromList [P [1],P [2,0]]) should reduce to S.fromList [P [1]]

S.fromList [P [1],P [2,0],P [2,1,0],P [3,0,0],P [3,-1,0]]
  should reduce to (at least)
    S.fromList [P [1],P [3,-1,0]]
  ideally to
    S.fromList [P [1]]

-}

smallest :: S.Set a -> S.Set a -> S.Set a
smallest xs ys = if S.size xs <= S.size ys then xs else ys

-- Compute a list of roots in the interval [0,1]
-- rootsP :: Field a => Poly a -> [a]
-- rootsP p = -- bracket the root

-- Perhaps avoid division (stay with Ring):
-- zoom a polynomial to the left of right half of the interval [0,1]
-- evalP (zoomPoly False p) (2*x  ) == evalP p x   -- x in [0,1/2]
-- evalP (zoomPoly True  p) (2*x-1) == evalP p x   -- x in [1/2,1]
-- zoomPoly :: Ring a => Bool -> Poly a -> Poly a
-- zoomPoly False ps =

{-
cmpZeroSpecial min max p | (cmpZero (derP (derP p)) == Just Le) --  (Assume 0<=p'')
                           && evalP derP min * evalP derP max < 0
--  given p, min, max where p' min * p' max < 0
    = -- let w = max-min
    findPolyBounds p
  how can we bound p to [pmin,pmax] (in [min,max])? [TODO]
  (we need to stop if w is too small)
  if 0<=pmin then we are done and 0<=p -> return Just Le
  if pmax<=0 then we are done and p<=0 -> return Just Ge
  if pmin*pmax<0 then we need to split further:
    let mid = (max+min)/2
        pmid = eval p mid
        p'mid = eval p' mid
    in if 0<=p'mid then recurse on [min,mid]
                   else recurse on [mid,max]
-}


ex1 :: (Ord a, P.Num a, Ring a) => S.Set (Poly a)
ex1 = S.fromList [P [2,4,-6,2],P [3,0,-4,2],P [3,1,-4,2],P [4,-5,2,0],P [4,-4,1,0],P [4,-3,1,0]]

-- return value is number of positive real roots plus an even number >= 0
-- thus, if 0 or 1, the function has that number of positive real roots.
-- otherwise, perhaps fewer.
decartesRuleOfSignsP :: (Ring a, Ord a) => Poly a -> Int
decartesRuleOfSignsP = decartesRuleOfSigns . unP
decartesRuleOfSigns :: (Ring a, Ord a) => [a] -> Int
decartesRuleOfSigns [] = 0
decartesRuleOfSigns (c:cs)  | c == zero  = decartesRuleOfSigns cs
                            | otherwise  = decartes' c cs

decartes' :: (Ring a, Ord a) => a -> [a] -> Int
decartes' _prev [] = 0
decartes' prev (c:cs) | c==zero || sameSign prev c = decartes' prev cs
                      | otherwise = 1 + decartes' c cs

sameSign :: (Ring a, Ord a) => a -> a -> Bool
sameSign x y = x*y >= zero


-- testDecartes = P.map (decartesRuleOfSigns . unP . derP) psdiff
-- testIncreasing = P.map (cmpZero . unP . derP . derP) psdiff
--

-- count number of roots between 0 and 1

type Work a = (a, Int, Poly a) -- c < 2^k, both natural numbers
type Interval a = (a, Int, a) -- c < 2^k, both natural numbers
-- (c, k, h) represents the interval [c,c+h]/2^{k}
-- q(x) = 2^{kn}*p((x+c)/2^{k}, where |n| is the degree of |p|
-- the polynomial q may be computed directly from p, c and k, but it is less costly to compute it incrementally, as it will be done in the decision tree; if p has integer coefficients, the same is true for q

{-
From wikipedia: https://en.wikipedia.org/wiki/Real-root_isolation

Pseudocode
The following notation is used in the pseudocode that follows.

p(x) is the polynomial for which the real roots in the interval [0, 1] have to be isolated
var(q(x)) denotes the number of sign variations in the sequence of the coefficients of the polynomial q
-}

squareFree :: (Eq a, Field a) => Poly a -> Bool
squareFree p = degree g <= 0
  where  g = gcdP p (derP p)
  -- check g = gcd p (derP p): if 1 then squareFree, else roots of g
  -- are multiple roots of p and they can be handled separately

-- numRoots computes the number of roots in the interval (0,1)
numRoots :: OrdField a => Poly a -> Int
numRoots = sum . numRoots'

-- Compute root multiplicities ([1,2] means 1 single and one double root)
numRoots' :: OrdField a => Poly a -> [Int]
numRoots' = P.map snd . filter (\((c,k,h),_) -> not (h==0 && k==0 && (c==zero || c==one))) . mulRoots

-- Compute all roots with multiplicities in the interval [0,1]. (Roots
-- are computed only up to a bracketing interval, but are guaranteed
-- to be distinct.)
mulRoots :: OrdField a => Poly a -> [(Interval a, Int)]
mulRoots p = let  ps  = yun p -- square-free factorisation
                  iss = P.map bisection ps
                  ims = concat (zipWith (\is m -> P.map (\i -> (i, m)) is) iss [1..])
             in ims

-- bisection computes a list of (sub-)intervals of [0,1] where each
-- interval has exactly one root.
bisection :: OrdField a => Poly a -> [Interval a]
bisection p | not (squareFree p) = error "bisection requires a square-free polynomial"
            | evalP p one  == zero  = (one,0,zero) : let (cs, rs) = divModP p (one-xP) in bisection cs
            | otherwise = bisection' (degree p) [(0,0,p)] []


bisection' :: (Ord a, Ring a) => Int -> [Work a] -> [Interval a] -> [Interval a]
bisection' n [] isol = isol
bisection' n (i@(c,k,q):l) isol = bisectStep1 n i l isol

bisectStep1 :: (Ord a, Ring a) => Int -> Work a -> [Work a] -> [Interval a] -> [Interval a]
bisectStep1 n i@(c,k,q) l isol =
  case zeroAtZero q of
    Just qdivx -> bisectStep2 (n-1) (c,k,qdivx) l ((c,k,zero):isol)
      -- "rational root found"
    Nothing -> bisectStep2 n i l isol

zeroAtZero :: (Eq a, Ring a) => Poly a -> Maybe (Poly a)
zeroAtZero (P []) = Just (P []) -- should never happen
zeroAtZero (P (c0:rest)) =
  if c0 == zero -- Same as |evalP q zero == zero|
  then Just (P rest) -- divide polynomial by x
  else Nothing

reverseCoeff :: (Eq a, Additive a) => Poly a -> Poly a
reverseCoeff p' = P (reverse cs)
  where cs = unP (normalPoly p')

xPlusOne :: Ring a => Poly a -> Poly a
xPlusOne p = comP p (P [one,one])

bisectStep2 :: (Ord a, Ring a) => Int -> Work a -> [Work a] -> [Interval a] -> [Interval a]
bisectStep2 n (c, k, q) l isol = if      v == 1  then  bisection' n l ((c,k,one):isol)
                                 else if v > 1   then  bisection' n (left:right:l) isol
                                                 else  bisection' n l isol
  where q' = xPlusOne (reverseCoeff q)  -- computes (x+1)^n*q(1/(x+1))
        v = decartesRuleOfSignsP q'
        qleft   = lefthalf   (computeFactors n) q
        qright  = righthalf  (computeFactors n) q
        left    = (2*c,    k+1,  qleft)
        right   = (2*c+1,  k+1,  qright)

-- lefthalf takes q to 2^{n}q(x/2)
{- Example:
  lefthalf (a0+a1*x+a2*x²)
== {- spec -}
  2^2 * (a0+a1*(x/2)+a2*(x/2)²)
== {- simplify -}
  2^2*a0 + 2^1*a1*x + a2*x²

The the pattern for lefthalf is
lefthalf factors (P cs) = P (zipWith (*) factors cs)
-}

lefthalf :: Ring a => [a] -> Poly a -> Poly a
lefthalf factors (P cs) = P (zipWith (*) factors cs)

-- righthalf computes 2^{n}q((x+1)/2)
{-
same as lefthalf after comP p (P [one,one])
-}

righthalf :: Ring a => [a] -> Poly a -> Poly a
righthalf factors p = comP (lefthalf factors p) (P [one, one])
-- righthalf factors p = lefthalf factors (comP p (P [one, one]))

computeFactors :: (Ring a) => Int -> [a]
computeFactors n = reverse (take (n+1) (iterate (two*) one))

-- Experiments ----------------------------------------------------------------
-- integral coeff polynomial with root in x=t/n
pr :: Ring a => a -> a -> Poly a
pr t n = P [-t, n]

testP1 :: Ring a => Poly a
testP1 = pr 2 3 * pr 6 10 * pr 2 7 * pr 1 5
evalI :: Field a => Interval a -> (a, a)
evalI (c, k, h) = (c/factor, (c+h)/factor)
  where factor = 2 ^+ k


eval :: Ring a => Poly Int -> a -> a
eval ps = evalP (fmap fromIntegral ps)
