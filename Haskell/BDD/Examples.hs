module BDD.Examples (module BDD.Examples, module Data.DecisionDiagram.BDD) where
import qualified Prelude as P (fromIntegral, map)
import Prelude (Ord, Bool(False, True), not, (||), and, or, Int, (+))
import qualified Data.IntMap as IM (fromList)
import Data.DecisionDiagram.BDD (BDD, ItemOrder, AscOrder, DescOrder,
                                 false, true, var, ite, (.||.), (.&&.), orB, andB, notB,
                                 restrict, pbAtLeast)
import BDD.Ordering ()

type Fun = BDD AscOrder
type Alg = BDD
type Index = Int

-- Note that the index is "global"
pick :: ItemOrder a => Index -> Alg a -> Alg a -> Alg a
pick i a0 a1 = ite (var i) a1 a0

-- Some simple example algorithms:
alg1 :: ItemOrder a => Alg a
alg1 = pick 1 (pick 2 false (var 3)) (pick 2 (var 3) true)
-- var i == pick i false true

alg1' :: ItemOrder a => Alg a
alg1' = pick 1 t t  -- this level is simplified away in the BDD
  where t = pick 2 false (var 3)

alg2 :: ItemOrder a => Alg a
alg2 = pick 1 t0 t1
  where t0 = pick 2 t00 t01
        t1 = pick 2 t01 t00
        t00 = var 3
        t01 = var 4

-----------------------------------fun AC------------------------------

fAC :: ItemOrder a => BDD a
fAC = notB (sameB as) .||. sameB cs
  where as = P.map var [1..3]
        cs = P.map var [4..5]

sameB :: ItemOrder a => [BDD a] -> BDD a
sameB bs = andB bs .||. notB (orB bs)

same :: [Bool] -> Bool
same bs = and bs || not (or bs)

-- Two BDDs with opposite variable orderings - they turn out to be
-- optimal for different probabilities of 1s.

-- start asking bits from index 1 upwards
ascfAC :: Alg AscOrder
ascfAC = fAC

-- start asking bits from index 5 downwards
descfAC :: Alg DescOrder
descfAC = fAC

---------------- MAJ2 ----------------

maj3 :: ItemOrder a => BDD a
maj3 = maj3' 1

maj3' :: ItemOrder a => Int -> BDD a
maj3' i = maj3'' (var i) (var (i+1)) (var (i+2))

maj3'' :: ItemOrder a => BDD a -> BDD a -> BDD a -> BDD a
maj3'' v1 v2 v3 =  (v1 .&&. v2) .||. (v1 .&&. v3) .||. (v2 .&&. v3)

maj2 :: ItemOrder a => BDD a
maj2 = maj3'' (maj3' 1) (maj3' 4) (maj3' 7)

maj2' :: ItemOrder a => Int -> BDD a
maj2' i = maj3'' (maj3' i) (maj3' (i+3)) (maj3' (i+6))

maj33 :: ItemOrder a => BDD a
maj33 = maj3'' (maj2' 1) (maj2' 10) (maj2' 19)

---------------- MAJ5 ----------------

maj5 :: Fun
maj5 = pbAtLeast (IM.fromList [(i,P.fromIntegral i) | i <- [1..5]]) 3
