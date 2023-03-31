{-# LANGUAGE FlexibleContexts #-}
module Util where

import Control.Monad (forM_, unless)
import Control.Monad.State (MonadState(..), execState)
import qualified Data.Set as Set


dfs :: (Ord a, MonadState (Set.Set a) m) => (a -> [a]) -> a -> m ()
dfs outgoing = h where
  h a = do
    visited <- get
    unless (Set.member a visited) $ do
      put $ Set.insert a visited
      forM_ (outgoing a) h

dfs' :: (Ord a) => (a -> [a]) -> a -> Set.Set a
dfs' outgoing start = execState (dfs outgoing start) Set.empty
