{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-
Algorithm generation.
-}

module Algor where
import qualified Prelude as P
import Prelude (Show, Ord, Eq, (==), Bool(..), Either(..), Int, Ordering(..), compare, Maybe(..), (.))
import qualified Data.Set as S (Set, singleton, toList, fromList, size, map)
import qualified Data.IntSet as IS (toList)
import qualified Data.IntMap as IM (fromList)
import Data.DecisionDiagram.BDD (BDD(Leaf, Branch), ItemOrder, AscOrder,
                                 support, restrict, var, substSet,
                                 Sig(SLeaf, SBranch), outSig)
import DSLsofMath.Algebra (Ring, zero, (+), (-), one, (*))
import DSLsofMath.PSDS (Poly, xP)
import PolyCmp (cmpPoly, OrdField)
import Thin(Thin(thin, cmp))
import BDD.Examples (Index, maj3, maj2, fAC)

{- We provide a separate type-class for (representations of) the boolean functions: -}

class BoFun f where
  isConst  :: f -> Maybe Bool
  setBit   :: Index -> Bool -> f -> f

{-
The |isConst| method allows us to check if the function is constant
(|Just b|), TODO update text: or if it can be seen as doing a case
split on index |i| with subfunctions |f0| and |f1| for the the |False|
and |True| cases respectively (|SBranch i f0 f1|).

The |setBit| method computes the subfunctions |setBit i False f| and
|setBit i True f| for each index |i|.

-}

-- use only when the function is constant
getLeaf :: BoFun a => a -> Bool
getLeaf t = case isConst t of Just b -> b; _ -> P.error "getLeaf: not a leaf"

genAlg :: (BoFun fun, Algor a, Ord a) => Int -> fun -> S.Set a
genAlg = genAlgStep genAlg

genAlgStep :: (BoFun fun, Algor a, Ord a) => (Int -> fun -> S.Set a) -> (Int -> fun -> S.Set a)
genAlgStep _genAlg _n fun | Just b <- isConst fun = S.singleton (res b)
genAlgStep  genAlg  n fun =
  S.fromList
    [ pic i p0 p1
    | i <- [1..n]
    , p0 <- S.toList (genAlg (n-1) (setBit i False fun))
    , p1 <- S.toList (genAlg (n-1) (setBit i True fun))
    ]

data Al = Res Bool | Pick Index Al Al
  deriving (Eq, Ord, Show)

al2Poly :: Ring a => Al -> Poly a
al2Poly (Res _b) = zero
al2Poly (Pick _i a0 a1) = one + (one-xP)*al2Poly a0 + xP*al2Poly a1

resPoly :: Ring a => Bool -> a
resPoly _b = zero
pickPoly :: Ring a => Index -> Poly a -> Poly a -> Poly a
pickPoly _i = pickPoly'

pickPoly' :: Ring a => Poly a -> Poly a -> Poly a
pickPoly' p0 p1 = one + (one - xP)*p0 + xP*p1

instance           Algor Al       where res = Res;      pic = Pick
instance Ring a => Algor (Poly a) where res = resPoly;  pic = pickPoly

-- Combine two computations in one, using only the first for comparisons.
data Both a b = Both a b deriving Show
instance (Algor a, Algor b) => Algor (Both a b) where res = resBoth; pic = picBoth
resBoth b = Both (res b) (res b)
picBoth i (Both a0 b0) (Both a1 b1) = Both (pic i a0 a1) (pic i b0 b1)

instance Ord a            => Eq    (Both a b)  where (==)     = eqFirst
instance Ord a            => Ord   (Both a b)  where compare  = compareFirst
instance (Ord a, Thin a)  => Thin  (Both a b)  where cmp      = cmpFirst
eqFirst       (Both a _)  (Both b _)  = EQ == compare a b
compareFirst  (Both a _)  (Both b _)  = compare a b
cmpFirst      (Both a _)  (Both b _)  = cmp a b

isConstBDD :: BDD a -> Maybe Bool
isConstBDD (Leaf b)  = Just b
isConstBDD _         = Nothing

-- compute the subfunction where index |i| has been eliminated
setBitBDD :: ItemOrder a => Index -> Bool -> BDD a -> BDD a
setBitBDD i b fun = substSet (IM.fromList [(j+1, var j) | j <- [i..n-1]]) (restrict i b fun)
  where n = P.maximum (IS.toList (support fun))

type BoolFun = BDD AscOrder
instance BoFun BoolFun where isConst = isConstBDD; setBit = setBitBDD

-- An "algorithm" is built like a tree with Index-labelled nodes and Boolean leaves.
class Algor a where
  res :: Bool -> a
  pic :: Index -> a -> a -> a
{- There are some hidden requirements: given a size |n :: Nat| and a
 function |f :: BoolFun n|, the leaf |res b| may be used only if the
 function always returns |b|, and otherwise |pic i t0 t1| can be used
 with |1<=i<=n| and with |t0| and |t1| being proper algorithms for the
 subfunctions when the bit |i| is set to |False| or |True|
 respectively. -}

-- Examples:

maj3A :: S.Set Al
maj3A = genAlg 3 (maj3 :: BoolFun)
maj3P :: S.Set (Poly Int)
maj3P = genAlg 3 (maj3 :: BoolFun)

{-
λ> S.size maj3A
12
λ> maj3P
fromList [P [2,2,-2]]
-}

fAC_A :: S.Set Al
fAC_A = genAlg 5 (fAC :: BoolFun)
fAC_P :: S.Set (Poly Int)
fAC_P = genAlg 5 (fAC :: BoolFun)
{-
λ> S.size fAC_A
54192
λ> S.size fAC_P
39
-}


maj2A :: S.Set Al
maj2A = genAlg 9 (maj2 :: BoolFun)
maj2P :: S.Set (Poly Int)
maj2P = genAlg 9 (maj2 :: BoolFun)
-- This probably takes a very long time to compute. Memoisation and thinning needed.

----------------
-- See Memo.hs for the momoization
-- Here we focus on *thinning*.

{-
The base case remains unchanged: a singleton set cannot be shrunk
In the step case: try first to just make one outer pass before returning

We express this using another class: |Thin|.
Note that we require a total order on |a| for the |Set| implementation, but that does not need to be compatible with the partial order |cmp|.
(It will affect the order of the steps in the thinning.)

-}

instance OrdField a => Thin (Poly a) where cmp = cmpPoly

{-
Here we abuse the |Ordering| type: we interpret |LT| as |<=|, not |<|, and similarly for |GT|.

-- TODO
-- coversAC :: Thin a => S.Set (AlgClass a) -> (AlgClass a) -> Bool
-- coversAC ps q = covers (S.map costPoly ps) (costPoly q)

-}

genAlgStepThin ::
  (Thin a, BoFun fun, Algor a) =>
  (Int -> fun -> S.Set a) ->
  (Int -> fun -> S.Set a)
genAlgStepThin genAlg n f = thin (genAlgStep genAlg n f)

genAlgThin :: (Thin a, BoFun fun, Algor a, Ord a) => Int -> fun -> S.Set a
genAlgThin = genAlgStepThin genAlgThin
