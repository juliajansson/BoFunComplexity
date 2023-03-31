{-# LANGUAGE FlexibleContexts #-}
module Util where

import Control.Arrow ((>>>), (&&&))
import Control.Monad (forM_, unless)
import Control.Monad.State (MonadState(..), execState)
import Data.Function.Memoize (Memoizable(..))
import Data.Functor.Classes (Eq1(..), Ord1(..), Show1(..), Eq2(..), Ord2(..), Show2(..))
import qualified Data.MultiSet as MultiSet
import qualified Data.Set as Set


mayTrace _ = id
--mayTrace = trace

shouldTrace _ = id
--shouldTrace = trace

instance (Ord a, Memoizable a) => Memoizable (MultiSet.MultiSet a) where
  memoize f = MultiSet.toAscOccurList >>> memoize (MultiSet.fromAscOccurList >>> f)

-- TODO: These should be in Data.MultiSet.
instance Eq1 MultiSet.MultiSet where
  liftEq eq' u v = liftEq (liftEq2 eq' (==)) u' v' where
    u' = MultiSet.toAscOccurList u
    v' = MultiSet.toAscOccurList v

instance Ord1 MultiSet.MultiSet where
  liftCompare compare' u v = liftCompare (liftCompare2 compare' compare) u' v' where
    u' = MultiSet.toAscOccurList u
    v' = MultiSet.toAscOccurList v

instance Show1 MultiSet.MultiSet where
  liftShowsPrec showsPrec' showList' p =
        MultiSet.toOccurList
    >>> liftShowList2 showsPrec' showList' showsPrec showList
    >>> (showString "fromOccurList " .)
    >>> showParen (p > 10)

naturals :: [Int]
naturals = iterate (+ 1) 0 

type Square x = (x, x)

duplicate :: x -> Square x
duplicate = id &&& id

-- Universal property of Bool.
-- This is a natural isomorphism.
-- TODO: find shorter names, perhaps use Iso' from lens library.
tabulateBool :: (Bool -> x) -> Square x
tabulateBool f = (f True, f False)

lookupBool :: Square x -> (Bool -> x)
lookupBool (a, b) v = if v then a else b

mapPair :: (a -> b) -> Square a  -> Square b
mapPair f = lookupBool >>> (f .) >>> tabulateBool

boolToInt :: Bool -> Int
boolToInt False = 0
boolToInt True = 1

unify :: (Eq a) => a -> a -> a
unify x y | x == y = x

dfs :: (Ord a, MonadState (Set.Set a) m) => (a -> [a]) -> a -> m ()
dfs outgoing = h where
  h a = do
    visited <- get
    unless (Set.member a visited) $ do
      put $ Set.insert a visited
      forM_ (outgoing a) h

dfs' :: (Ord a) => (a -> [a]) -> a -> Set.Set a
dfs' outgoing start = execState (dfs outgoing start) Set.empty
