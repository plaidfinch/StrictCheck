module Test.StrictCheck.Consume
  ( Input
  , Inputs
  , Consume(..)
  , fields
  , consumeTrivial
  , consumeCoArbitrary
  ) where

import Test.QuickCheck
import qualified Data.Urn as Urn
import GHC.Generics

import Test.StrictCheck.Internal.Inputs


-------------------------------------------------------
-- The user interface for creating Consume instances --
-------------------------------------------------------

-- | Generate a tree of all possible ways to destruct the input value.
class Consume a where
  consume :: a -> Input
  default consume :: (Generic a, GFields (Rep a)) => a -> Input
  consume x = fields (gFields (from x) [])

-- | Reassemble pieces of input into a larger Input. The Words are weights which
-- determine the relative probability of continuing to pattern match in that
-- subpart of the input.
fields :: [Input] -> Input
fields =
  Input . Urn.fromList .
    zipWith (\v input ->
               (1, (Variant (variant v), input)))
            [(0 :: Int) ..]

-- | Use the CoArbitrary instance for a type to consume it. This should only be
-- used for "flat" types, i.e. those which contain no interesting substructure.
consumeCoArbitrary :: CoArbitrary a => a -> Input
consumeCoArbitrary !a =
  Input . Just . Urn.singleton 1 $
    (Variant (coarbitrary a), Input Nothing)

-- | If a type has no observable properties or substructure which can be used
-- to drive the randomization of output, consumption should merely evaluate a
-- value to weak-head normal form.
consumeTrivial :: a -> Input
consumeTrivial !_ = Input Nothing

-- | Functions can be trivially consumed.
instance Consume (a -> b) where
  consume = consumeTrivial


--------------------------------------------
-- Deriving Consume instances generically --
--------------------------------------------

-- | gFields produces a difference list corresponding to the consumed inputs of
-- all fields in the data structure. It correctly handles nesting: that is, like
-- a handwritten instance of Consume, it places all fields from the same
-- constructor within the same "level" of the Input, so that they are all
-- simultaneously exposed for destruction when the constructor is forced.

-- NOTE: gFields produces a difference list because we can't rely on Generics to
-- give us a right-nested sequence of product constructors. If there is left-
-- nesting, the naive implementation would suffer from quadratic slowdown. The
-- use of a difference list reassociates all the appending to make sure it's
-- linear.

class GFields f where
  gFields :: f p -> ([Input] -> [Input])

instance GFields V1 where
  gFields _ = id

instance GFields U1 where
  gFields !U1 = id

instance (GFields f, GFields g) => GFields (f :+: g) where
  gFields (L1 x) = gFields x
  gFields (R1 x) = gFields x

instance (GFields f, GFields g) => GFields (f :*: g) where
  gFields (x :*: y) = gFields x . gFields y

instance (GFields f) => GFields (M1 i t f) where
  gFields (M1 x) = gFields x

instance (Consume c) => GFields (K1 i c) where
  gFields (K1 x) = (consume x :)
