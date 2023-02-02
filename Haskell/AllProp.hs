{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RebindableSyntax #-}
module AllProp (module All, module AllProp, module S) where
import Prelude hiding (map, Num(..),Fractional(..), fromIntegral, sum, product)
import qualified Prelude as P
import Test.QuickCheck

import DSLsofMath.PSDS as Poly (Poly(P), xP, evalP, degree)
import DSLsofMath.Algebra (Ring, zero, (+), (-), one, (*), negate, fromInteger, Field, fromRational, (/))

import Data.Maybe (isNothing)
import qualified Data.Set as S
  (  Set, singleton, toList, fromList, foldl
  ,  size, map, member, insert, empty, isSubsetOf, (\\)
  )
import All

-- Because of RebindableSyntax
ifThenElse :: Bool -> a -> a -> a
ifThenElse True  a _ = a
ifThenElse False _ b = b

-- ----------------
-- Properties we want from the "thin" set

{-
let xs = thin ys :: {a} and (<=) :: a -> a -> Bool

p1. |xs| is a subset of |ys|
p2. |xs| is Pareto efficient (all elems are mutually incomparable)
p3. |xs| strictly dominates |ys \\ xs|

Can we preserve all these properties in the recursion?

-}

p1 :: Ord a => S.Set a -> S.Set a -> Bool
p1 = S.isSubsetOf

p2 :: Thin a => S.Set a -> Bool
p2 = isParetoEff 

p3 :: Thin a => S.Set a -> S.Set a -> Bool
p3 xs ys = all  (\ y -> any (<< y) xs)
                (ys S.\\ xs)

isParetoEff xs = all (\ x -> all (indiff (<<) x) xs) xs

indiff :: (a -> a -> Bool) -> a -> a -> Bool
indiff r x y = not (r x y) && not (r y x) 

-- strictly dominates
(<<) :: Thin a => a -> a -> Bool
x << y = cmp x y == Just LT

isParetoFront xs ys = p1 xs ys && p2 xs && p3 xs ys

spec n f = head (fst (spec' n f))
spec' :: Int -> BDDFun -> ([Bool], (S.Set (Poly Rational), S.Set (Poly Rational)))
spec' n f = 
  let  ys = genAlg n f
       xs = genAlgThinMemoPoly n f
  in ( [ isParetoFront xs ys
       , p1 xs ys
       , p2 xs
       , p3 xs ys
       ]
     , (xs, ys)
     )

runTests = do
  print (spec 3 maj3)
  print (spec 5 fAC)

{- main question:
Can we prove spec ?

Base case: spec n (const b)
  ys = { res b }
  xs = thin { res b } = { res b }
properties trivially satisfied.
-}

baseCase :: Int -> Bool -> Bool
baseCase n b =
  let f = if b then true else false
  in spec n f

{-

Step case:
  We can assume
    ih i b = spec n (setBit i b f)
  for all i in 1..n+1, b in Bool
  We want to prove spec (n+1) f


-- Here is a test for the step case. (Can be very computationally
-- intensive.)

-}

stepCase :: Int -> BDDFun -> Property
stepCase n f =
  let ih i b = spec (n-1) (setBit i b f)
  in and [ih i b | i <- [1..n], b <- [False, True]] ==> spec n f

-- False  ==> q = True
-- True   ==> q = q

{-

Three properties to prove:
  p1 - being a subset - should be easy
    xs i b `isSubsetOf` ys i b
  p2 - simple propery of thin (strict)
    (not necessary for correctness)
  p3 - xs dominates ys
    here is where polynomial calculation comes in

Pre-writing:

-- "covering" or "domination"
xs Cs ys =def= Forall y in ys. Exists x in xs. x << y
In words: every element in ys is covered by som element in xs

Alt. formulation:

xs Cs ys =def= Forall y in ys. xs C y
xs C  y  =def= Exists x in xs. x << y


{- Wikipedia: a is covered by b if a<b and no other c fits in between. That is not what we mean by "cover". -}

Starting point:
  preorder (<<=) : a -> a -> Bool
    =def= reflexive (<<=) && transitive (<<=)
accompanied by a strict preorder _induced_ by (<<=):
  x << y =def= x <<= y && not (y <<= x)

For our polynomial use-case:

 p <<= q =def= Forall x in [0,1]. p x <= q x

 p << q =def=
   (Forall x in [0,1]. p x <= q x) && not (Forall x in [0,1]. q x <= p x)
 = 
   (Forall x in [0,1]. p x <= q x) && Exists x in [0,1]. q x > p x
 = 
   (Forall x in [0,1]. p x <= q x) && Exists x in [0,1]. p x < q x

With p and q polynomials, the "Exists" part also implies there is an eps-neighbourhood in which p x < q x. As a consequence, Exists x in (0,1). p x < q x. This helps in the induction step of the proof.






-}

-- ----------------
-- Thinning properties

s1 :: (Ord a, Ring a) => S.Set (Poly a)
s1 = S.fromList [P [1],P [2],P [2,1],P [3],P [3,-1]]

s2 :: (Ord a, Ring a) => S.Set (Poly a)
s2 = S.fromList [P [1,1], P [1, 2], P [2,-1], P [3,-2], P [3,-3]]

-- I want to find an example where the polynomial order disagrees with the lexicographic order.
-- p << q but p > q

instance Arbitrary a => Arbitrary (Poly a) where arbitrary = arbitraryP

arbitraryP :: Arbitrary a => Gen (Poly a)
arbitraryP = fmap P arbitrary

-- We have P [-1] << P [] but P[-1] > P []
-- Are there examples of higher degree?
prop_Order1 :: (Ord a, Ring a, Thin (Poly a)) => Poly a -> Poly a -> Property
prop_Order1 p q = (degree p > 0 && not (q << p)) ==> p < q
prop_Order2 :: (Ord a, Ring a, Thin (Poly a)) => Poly a -> Poly a -> Property
prop_Order2 p q = (degree p > 0 && p < q) ==> not (q << p)

test1 = quickCheck (\p -> prop_Order1 (p :: Poly Rational))
test2 = quickCheck (\p -> prop_Order2 (p :: Poly Rational))

ex1, ex2 :: Poly Rational
ex1 = P [0.21, 2.2, 0.72]
ex2 = P [0.28, 2.4]
-- ex1 = P [1947289208813 % 8978429546345,3935293041523 % 1789427546168,6707908764248 % 9329591219367]
-- ex2 = P [1025329623607 % 3703736031601,51240612152 % 21302069735]








