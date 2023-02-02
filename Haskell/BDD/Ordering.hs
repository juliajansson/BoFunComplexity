module BDD.Ordering where
import Data.DecisionDiagram.BDD (BDD(Leaf, Branch), numNodes)
{- Ordering BDDs (to enable use of Data.Map from BDDs to enumerations)
 Note that the ordering does not have a sensible meaning in terms of
 the underlying boolean functions, it just makes sure the set of BDDs
 is ordered so that we can use efficient datastructures on it.
-}
instance Ord (BDD a)  where  compare = compareBDD

-- smaller BDDs sort first, then Leaf < Branch
compareBDD :: BDD a -> BDD a -> Ordering
compareBDD x y = thenCmp (compare (numNodes x) (numNodes y))
                         (compareBDD' x y)

thenCmp :: Ordering -> Ordering -> Ordering
thenCmp EQ o2 = o2
thenCmp o1 _  = o1

-- This uses the "smart patterns" defined in the BDD module
compareBDD' :: BDD a -> BDD a -> Ordering
compareBDD' (Leaf x) (Leaf y) = compare x y
compareBDD' (Leaf x) _        = LT
compareBDD' _        (Leaf y) = GT
compareBDD' (Branch li l0 l1) (Branch ri r0 r1) = compare (li, l0, l1) (ri, r0, r1)
