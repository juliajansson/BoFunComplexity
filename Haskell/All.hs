{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeSynonymInstances #-}
module All (module All, module BDD.Examples, module S, module Poly, module BDD) where
import Prelude hiding (map, Num(..),Fractional(..), fromIntegral, sum, product)
import qualified Prelude as P
import qualified Data.Set as S (Set, singleton, toList, fromList, foldl,
                                size, map, member, insert, empty, filter)
import qualified Data.IntSet as IS (toList)
import qualified Data.IntMap as IM (fromList)
import DSLsofMath.PSDS as Poly (Poly(P), xP, evalP)
import DSLsofMath.Algebra (Ring, zero, (+), (-), one, (*))
import Data.DecisionDiagram.BDD as BDD
  (  BDD(Leaf, Branch), ItemOrder, AscOrder
  ,  support, restrict, var, substSet, false, true
  ,  Sig(SLeaf), inSig, outSig)
import Data.Function.Memoize (Memoizable(memoize), memoFix, memoFix2, deriveMemoizable, traceMemoize)
import BDD.Examples (Index, maj3, maj2, fAC, maj33)
-- see paper 2.4
import PolyCmp (cmpPoly, OrdField)
-- see paper 3.4
import Debug.Trace

{-
From the BDD library:

data Sig f = SLeaf Bool | SBranch Int f f
  -- we only use the SLeaf branch, otherwise we use setBit to get to the children (for different i than what the BDD has used)
type BDD ≃ Sig BDD

-}

----------------------------------------------------------------
-- import Algor (BoolFun, genAlgStep, genAlgStepThin)
-- TODO paper: explain the minimal interface
class BoFun f where
  isConst  :: f -> Maybe Bool -- Sig f
  setBit   :: Index -> Bool -> f -> f

{-
TODO properties?
if isConst f == Just b
then isConst (setBit i b f) for all i and b
-}

isConstBDD :: BDD a -> Maybe Bool
isConstBDD x = case outSig x of
  SLeaf b -> Just b
  _       -> Nothing

-- compute the subfunction where index |i| has been eliminated (set to b)
setBitBDD :: ItemOrder a => Index -> Bool -> BDD a -> BDD a
setBitBDD i b fun = substSet (IM.fromList [(j+1, var j) | j <- [i..n-1]]) (restrict i b fun)
  where n = P.maximum (IS.toList (support fun))

type BDDFun = BDD AscOrder
instance BoFun BDDFun where isConst = isConstBDD; setBit = setBitBDD


class Algor a where  -- TODO check naming: DecTree? Alg?
  res :: Bool -> a
  pic :: Index -> a -> a -> a

-- TODO perhaps name it DecTree to match paper
data Al = Res Bool | Pick Index Al Al
  deriving (Eq, Ord, Show)

index :: [a] -> Int -> a
index t i = t!!(i-1)

-- start of index manipulation
type GAl = Al
local2Global :: [Index] -> Al -> GAl
local2Global _rem (Res b) = Res b
local2Global rem (Pick i a0 a1) = Pick (index rem i) g0 g1
  where  rem' = remove i rem
         g0 = local2Global rem' a0
         g1 = local2Global rem' a1

remove :: Index -> [a] -> [a]
remove i xs = let (as, bs) = splitAt (i-1) xs in as ++ drop 1 bs

loc2Glob :: Int -> Al -> GAl
loc2Glob n = local2Global [1..n]
-- end of index manipulation

foldAlgor :: Algor a => Al -> a
foldAlgor (Res b) = res b
foldAlgor (Pick i a0 a1) = pic i (foldAlgor a0) (foldAlgor a1)

type Tup = [Bool]
type CostFun = Tup -> Int

resC :: Bool -> CostFun
resC b = const 0
pickC i c0 c1 = \t -> let t' = remove i t
                       in 1 + if index t i then c1 t' else c0 t'

instance Algor CostFun where res = resC; pic = pickC

--Julia: Added maxcost, not sure if it works though
type MaxCost = Int
pickMC i m1 m2 = 1 + max m1 m2
instance Algor MaxCost where res = const 0; pic = pickMC

resPoly :: Ring a => Bool -> a
resPoly _b = zero
pickPoly :: Ring a => Index -> Poly a -> Poly a -> Poly a
pickPoly _i = pickPoly'

pickPoly' :: Ring a => Poly a -> Poly a -> Poly a
pickPoly' p0 p1 = one + (one - xP)*p0 + xP*p1

instance           Algor Al       where res = Res;      pic = Pick
instance Ring a => Algor (Poly a) where res = resPoly;  pic = pickPoly


type BoolFun = Tup -> Bool
resB :: Bool -> BoolFun
resB = const
picB :: Index -> BoolFun -> BoolFun -> BoolFun
picB i f0 f1 = \t -> if index t i then f1 t else f0 t
instance Algor BoolFun where res = resB; pic = picB

type Path = [(Index,Bool)]
type EvalPath = Tup -> Path
resEP :: Bool -> EvalPath
resEP b = const []
picEP :: Index -> EvalPath -> EvalPath -> EvalPath
picEP i ep0 ep1 = \t -> let b = index t i in (i,b) : if b then ep1 t else ep0 t

instance Algor EvalPath where res = resEP; pic = picEP

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

-- Naive version (see Algor.hs:56)
genAlg :: (BoFun fun, Algor a, Ord a) => Int -> fun -> S.Set a
genAlg = genAlgStep genAlg
-- genAlg = fix genAlgStep

-- The core computation step
genAlgStep ::  (BoFun fun, Algor a, Ord a) =>
               (Int -> fun -> S.Set a) ->
               (Int -> fun -> S.Set a)
genAlgStep _genAlg _n fun
  | Just b <- isConst fun = S.singleton (res b)
genAlgStep  genAlg  n fun =
  S.fromList
    [ pic i p0 p1
    | i   <- reverse [1..n]
--    | i <- [1..n]
    , p0  <- S.toList (genAlg (n-1) (setBit i False  fun))
    , p1  <- S.toList (genAlg (n-1) (setBit i True   fun))
    ]

----------------------------------------------------------------
-- import Thin
class Ord a => Thin a where
  cmp  :: a -> a -> Maybe Ordering

  checkLTE :: a -> a -> Bool
  checkLTE p q = cmp p q `elem` [Just LT, Just EQ]
  checkLT :: a -> a -> Bool
  checkLT p q = cmp p q == Just LT

  covers    :: S.Set a -> a -> Bool   -- <<. "domination"
  thin      :: S.Set a -> S.Set a
  thinFrom  :: S.Set a -> S.Set a -> S.Set a
  thinStep  :: S.Set a -> a -> S.Set a

  -- default definitions
  thin = thinFrom S.empty
  thinFrom = S.foldl thinStep
--  thinStep xs x = if covers xs x then xs else thinFrom (S.singleton x) xs
  thinStep xs x = if covers xs x then xs else S.insert x xs
-- The following is the "optimal" (quadratic) thinning
--  thinStep xs x = if covers xs x then xs else
--    S.insert x (S.filter (not . (x `checkLT`)) xs)
--  thinStep xs x = if covers xs x then xs else myInsert x xs
    -- TODO check if xs can be thinned
  covers ps q = S.member True (S.map (`checkLTE` q) ps)

{-
-- TODO: Perhaps use this (adapted from the ADwH book)
-}
thinBy (<<) = foldr gstep S.empty
  where gstep x ys = if any (<< x) ys -- ys <<. x  "ys dominates x"
                        then ys
                        else S.insert x (S.filter (not . (x <<)) ys)


myInsert :: Thin a => a -> S.Set a -> S.Set a
myInsert x = thinFrom (S.singleton x)

instance OrdField a => Thin (Poly a) where cmp = cmpPoly

-- To turn off thinning (for testing) use this:
-- instance OrdField a => Thin (Poly a) where cmp = cmpPoly; thin = id

-- To add tracing of the calls to thin use this:
-- instance OrdField a => Thin (Poly a) where cmp = cmpPoly; thin = thinTrace
-- thinTrace xs = trace (show (S.size xs)) (thinFrom S.empty xs)

instance Thin Al where cmp _ _ = Nothing; thin = id

genAlgStepThin ::
  (Thin a, BoFun fun, Algor a) =>
  (Int -> fun -> S.Set a) ->
  (Int -> fun -> S.Set a)
-- genAlgStepThin genAlg n f = thin (genAlgStep genAlg n f)
-- Use this variant to check the number of recursive calls made
genAlgStepThin = genAlgStepThinTrace
genAlgStepThinTrace genAlg n f =
  let ys = genAlgStep genAlg n f
      xs = thin ys
  in  trace (show n ++ ";" ++ show (S.size ys) ++ ";" ++ show (S.size xs)) $
      xs
-- Note: perhaps show all the polynomials (for fAC) [needs Show class constraints...]
--  in  trace (show n ++ ";" ++ show (S.size ys) ++ ";" ++ show (S.size xs) ++
--            ";ys=" ++ show ys++";xs="++show xs) $

----------------------------------------------------------------

$(deriveMemoizable ''Sig)

instance Memoizable BDDFun where memoize = memoizeBF

memoizeBF :: (BDDFun -> a) -> (BDDFun -> a)
memoizeBF f = memoize (f . inSig) . outSig
-- To log a trace of the memoize calls:
-- memoizeBF f =traceMemoize (f . inSig) . outSig
-- Sig BDDFun ~ Either Bool (Index,BDDFun,BDDFun)

genAlgMemo :: Int -> BDDFun -> S.Set (Poly Int)
genAlgMemo = memoFix2 genAlgStep

genAlgThinMemo' :: (BoFun fun, Memoizable fun, Thin a, Algor a) => Int -> fun -> S.Set a
genAlgThinMemo' = memoFix2 genAlgStepThin

genAlgThinMemoPoly :: Int -> BDDFun -> S.Set (Poly Rational)
genAlgThinMemoPoly = genAlgThinMemo'

genAlgThinMemoBoth :: Int -> BDDFun -> S.Set (Both (Poly Rational) Al)
genAlgThinMemoBoth = genAlgThinMemo'

ps9 = genAlgThinMemoPoly 9 maj2
main = print ps9
check9 = ps9 == S.fromList [P [4,4,6,9,-61,23,67,-64,16]]

ps5 = genAlgThinMemoPoly 5 fAC
test5 = print ps5
as5 = genAlgThinMemo' 5 (fAC :: BDDFun) :: S.Set Al
test5Al = print as5
as5' = genAlg 5 (fAC :: BDDFun) :: S.Set Al
ps5' = genAlg 5 (fAC :: BDDFun) :: S.Set (Poly Rational)

check5 = ps5 == S.fromList [  P [2,6,-10,8,-4],  P [4,-2,-3,8,-2],
                              P [5,-8, 9,0,-2],  P [5,-8,8]        ]

-- This gets killed by the OS after using up too much memory
test27 = print (genAlgThinMemoPoly 27 maj33)
