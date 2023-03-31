{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE UndecidableInstances #-}
module BoFun where

import Data.Function ((&))
import qualified Data.Set as Set
import Data.Void (Void, absurd)

import Debug.Trace

import Util


class BoFun f i | f -> i where
  isConst   :: f -> Maybe Bool
  variables :: f -> [i]
  -- TODO: return function i -> i that explains how the variables got renamed?
  setBit    :: (i, Bool) -> f -> f

viewConst :: BoFun f i => f -> Either Bool f
viewConst f = maybe (Right f) Left (isConst f)

-- These two instances are not yet used.
{-
instance BoFun Void Void where
  isConst = absurd
  variables = absurd
  setBit _ = absurd

instance (BoFun f i, BoFun g j) => BoFun (Either f g) (Either i j) where
  isConst (Left f) = isConst f
  isConst (Right g) = isConst g

  variables (Left f) = f & variables & map Left
  variables (Right g) = g & variables & map Right

  setBit (Left i, val) (Left f) = f & setBit (i, val) & Left
  setBit (Right j, val) (Right g) = g & setBit (j, val) & Right
-}

{-
* Nothing represents the identity function.
* Just val represents the constant function with value val.
-}
instance BoFun (Maybe Bool) () where
  isConst = id
  variables = maybe [()] $ const []
  setBit ((), val) Nothing = Just val

outgoing :: (BoFun f i) => f -> [f]
outgoing u = do
  v <- variables u
  val <- [True, False]
  return $ setBit (v, val) u

reachable :: (Ord f, BoFun f i) => f -> Set.Set f
reachable = dfs' outgoing
