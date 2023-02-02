{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
module Memo where
import Data.Function.Memoize (Memoizable(memoize), memoFix2, deriveMemoizable)
import qualified Data.Set as S (Set)
import DSLsofMath.PSDS (Poly)
import Data.DecisionDiagram.BDD (Sig, inSig, outSig)
import BDD.Examples (maj2, maj33)
import Algor (BoolFun, genAlgStep, genAlgStepThin)

{-
Memoisation

When computing the set of algorithms for a given function (of |n|
bits), the recursive calls will compute the corresponding sets of
algorithms for some functions of |n-1| bits. Often, some of these
subfunctions are the same, but will be recomputed unless we take
special care in storing the earlier results. And even if the immediate
subfunctions are different, there are often overlaps further down in
the call graph.

The classical solution to the problem of recomputing is memoisation
and there are several papers describing how to set this up for
different datastructures.  Based on the type structure of the domain
of the function, a suitable type of memo-table is formulated and then
populated with data as they are computed.

DONE: check if some standard solution is applicable - yes!

-}

$(deriveMemoizable ''Sig)

instance Memoizable BoolFun where memoize = memoizeBF

memoizeBF :: (BoolFun -> a) -> (BoolFun -> a)
-- memoizeBF f = traceMemoize (f . sig2BF) . bf2Sig
memoizeBF f = memoize (f . sig2BF) . bf2Sig
-- memoizeBF f = memoize (f . al2BF) . bf2Al
-- memoizeBF f = traceMemoize (f . al2BF) . bf2Al
-- Add the trace to see the calls which are not in the table

bf2Sig :: BoolFun -> Sig BoolFun
bf2Sig = outSig

sig2BF :: Sig BoolFun -> BoolFun
sig2BF = inSig

genAlgMe :: Int -> BoolFun -> S.Set (Poly Int)
genAlgMe = memoFix2 genAlgStep

genAlgThinMe :: Int -> BoolFun -> S.Set (Poly Rational)
genAlgThinMe = memoFix2 genAlgStepThin

main = print (genAlgThinMe 9 maj2)

-- This gets killed by the OS after using up too much memory
test = print (genAlgThinMe 27 maj33)


----------------------------------------------------------------
-- Unused
{-
import Data.DecisionDiagram.BDD (BDD(Leaf, Branch), fold)

$(deriveMemoizable ''Al)

foldAl :: (Index -> a -> a -> a) -> (Bool -> a) -> Al -> a
foldAl branch leaf = go
  where  go (Pick i a0 a1)  = branch i (go a0) (go a1)
         go (Res b)         = leaf b

al2BF :: Al -> BoolFun
al2BF = foldAl Branch Leaf

bf2Al :: BoolFun -> Al
bf2Al = fold Pick Res
-}
