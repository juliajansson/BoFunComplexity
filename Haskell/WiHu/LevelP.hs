-- code by Liam Hughes (work in progress)
{-# LANGUAGE LambdaCase #-}
module LevelP where

import Data.Map (Map(..))
import qualified Data.Map as M
--Nested modules would let me avoid this boilerplate...

import Control.Monad.State

--Idea: preserve higher-level combinators such as majority in the graph.
--maj/count greater or equal n has the nice property (like and, or, xor) that
--it's commassoc.
--That means the list of arguments can be represented as a bag.
--Special case: I assume each variable is present only once.

--Algorithm: for each isomorphically distinct var, try evaluating it and
--normalize the resulting tree; memoize the expected cost.
--For maj3^2, the state is <= 3^3
--For maj3^3, it should be <= 27^3 - well within the range of practicality.

--Formula trees
data Formula = Var --Leaf
             | CGE Int Bag --Count (of true args) greater than or equal to
             | FALSE                          -- could also be CGE 1 empty
             | TRUE --Used for normalization  -- could also be CGE 0 empty
  deriving (Eq,Ord,Read,Show)

--The Integers can only be positive
type Bag = Map Formula Integer   -- [(Formula,Nat)]
-- CGE 1 (2*Var) ~= x1 || x2
-- CGE 2 (3*Var) ~= maj3      
-- CGE 2 (3*(CGE 2 (3*Var))) ~= maj3^2
-- closed under "setBit i b"


--Default filter omitted for perf
add :: Bag -> Bag -> Bag
add = M.unionWith (+)

scale :: Integer -> Bag -> Bag
scale = M.map . (*)

--The result of evaluating one subexpr in a bag
--Assumes b[from] >= 1
--If an argument in a CGE is FALSE, just delete it; if it's TRUE, delete it
--and decrement the count.
replace :: Formula -> Formula -> Bag -> Bag
replace from to = M.filter (>0) . add (M.fromList [(from,-1),(to,1)])

--This could be optimized using a stack of return continuations
--Maybe having un-normalized formulae be the same type is a mistake...
--Assumes the target for modification is a CGE n b with n > 0 and b[from]>0
--CGE 0 b = TRUE
--CGE (n>0) {} = FALSE
normReplace :: Formula -> Formula -> Formula -> Formula
normReplace (CGE n b) from | n <= 0 || M.lookup from b == Nothing = error "normReplace: Bad precond"
  | otherwise = \case
  FALSE ->
    let b' = M.filter (>0) $ add (M.fromList [(from,-1)]) b
    in cge n b'
  TRUE ->
    let n' = n - 1
        b' = M.filter (>0) $ add (M.fromList [(from,-1)]) b
    in cge n' b'
  to -> CGE n (replace from to b)

cge 0 b = TRUE
cge n b | b == M.empty = FALSE
        | otherwise    = CGE n b


--Note: only graphs with an equal number of vars can be isomorphic.
--Consequently, I could use an array of maps rather than a single map for
--memoization.

type Path = [Int]
data DecisionTree = Answer Bool                          -- Res
                  | Eval Path DecisionTree DecisionTree  -- Pick i t0 t1
                  --The Path indicates the list of keys by index
  deriving (Eq,Ord,Read,Show)

-- implicitly assumes a probability p as a parameter
type Memotable = Map Formula (Double,DecisionTree)  -- expected cost for an optimal tree (and such a tree) 
--The tree will be very large, but also very shared... TODO make sharing
--explicit so one can persist and ppr the tree.
--2^27 is 128M...

--decision tree, expected cost (# vars evaluated before answer)
--First answer: FALSE, second: TRUE
--p = the probability each var is true
--Double is first so we can sort by it
solve :: Double -> Formula -> State Memotable (Double,DecisionTree)
solve p = \case
  FALSE -> return (0,Answer False)
  TRUE  -> return (0,Answer True)
  t -> do
    memo <- get
    case M.lookup t memo of
      Just ret -> return ret
      Nothing -> do
        candidates <- mapM (\(path,f0,f1) -> do
                               (cost0,dt0) <- solve p f0
                               (cost1,dt1) <- solve p f1
                               return (1 + (1-p)*cost0 + p*cost1,
                                       Eval path dt0 dt1)
                           )
                           (step t)
        let best | null candidates  = error "solve: Bad"
                 | otherwise        = minimum candidates
        modify (M.insert t best)
        return best
        
solver :: Double -> Formula -> (Double,DecisionTree)
solver p f = evalState (solve p f) M.empty

-- | A function tree => list of pairs of trees with one var evaluated
-- (modulo symmetry)  -- basically {(i, setBit i False f, setBit i True f) | i <- all var paths}
--Also returns the path to the var modified
--Since all vars have equal p, I don't need to mention the p
--Do normalization as part of this step to avoid multiple traversals
step :: Formula -> [(Path,Formula,Formula)]
step = \case Var -> [([],FALSE,TRUE)]
             cge@(CGE n b) -> do
               --For each k in b, normReplace k with k' <- step k
               (ix,f) <- zip [0..] $ M.keys b
               (path,f0,f1) <- step f
               return (ix:path,
                       normReplace cge f f0,
                       normReplace cge f f1)

--Functions for building formulae ergonomically, using argument lists
maj :: [Formula] -> Formula
maj xs = CGE (succ $ length xs `div` 2) $ listToBag xs

majN n x = maj $ replicate n x

listToBag :: [Formula] -> Bag
listToBag = foldr add M.empty . map (flip M.singleton 1)

ex1 = majN 3 $ majN 3 Var

maj3 = majN 3 Var

test p = solver p maj3
test2 p = runState (solve p maj3) M.empty

{-
((2.875,
  Eval [0] (Eval [0] (Eval [0] (Answer False) (Eval [0] (Answer False) (Answer True))) (Eval [0] (Answer False) (Answer True))) (Eval [0] (Eval [0] (Answer False) (Answer True)) (Answer True))),

 fromList
  [(CGE 1 (fromList [(Var,0)]),   (1.0,Eval [0] (Answer False) (Answer True))),
   (CGE 1 (fromList [(Var,1)]),   (1.0,Eval [0] (Answer False) (Answer True))),
   (CGE 1 (fromList [(Var,2)]),   (1.5,Eval [0] (Eval [0] (Answer False) (Answer True)) (Answer True))),
   (CGE 2 (fromList [(Var,1)]),   (1.5,Eval [0] (Answer False) (Eval [0] (Answer False) (Answer True)))),
   (CGE 2 (fromList [(Var,2)]),   (2.25,Eval [0] (Eval [0] (Answer False) (Eval [0] (Answer False) (Answer True))) (Eval [0] (Answer False) (Answer True)))),

   (CGE 2 (fromList [(Var,3)]),   (2.875,Eval [0] (Eval [0] (Eval [0] (Answer False) (Eval [0] (Answer False) (Answer True))) (Eval [0] (Answer False) (Answer True))) (Eval [0] (Eval [0] (Answer False) (Answer True)) (Answer True))))])
λ> 
-}
