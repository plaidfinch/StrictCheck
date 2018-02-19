module Test.StrictCheck.Consume
  ( Input
  , Inputs
  , Consume(..)
  , constructor
  , normalize
  , consumeTrivial
  , consumePrimitive
  ) where

import Test.QuickCheck
import Generics.SOP
import Generics.SOP.NS

import Test.StrictCheck.Internal.Inputs


-------------------------------------------------------
-- The user interface for creating Consume instances --
-------------------------------------------------------

-- | Generate a tree of all possible ways to destruct the input value.
class Consume a where
  consume :: a -> Input
  default consume :: GConsume a => a -> Input
  consume = gConsume

-- | Reassemble pieces of input into a larger Input.
constructor :: Int -> [Input] -> Input
constructor n !is =
  Input (Variant (variant n)) is

-- | Use the CoArbitrary instance for a type to consume it. This should only be
-- used for "flat" types, i.e. those which contain no interesting substructure.
consumePrimitive :: CoArbitrary a => a -> Input
consumePrimitive !a =
  Input (Variant (coarbitrary a)) []

-- | If a type has no observable properties or substructure which can be used
-- to drive the randomization of output, consumption should merely evaluate a
-- value to weak-head normal form.
consumeTrivial :: a -> Input
consumeTrivial !_ =
  Input mempty []

-- | Functions can be trivially consumed.
instance Consume (a -> b) where
  consume = consumeTrivial

-- | Fully normalize something which can be consumed
normalize :: Consume a => a -> ()
normalize (consume -> input) = go input
  where
    go (Input _ is) = foldr seq () (map go is)

--------------------------------------------
-- Deriving Consume instances generically --
--------------------------------------------

type GConsume a = (Generic a, All2 Consume (Code a))

gConsume :: GConsume a => a -> Input
gConsume !(from -> sop) =
  constructor (index_SOP sop)
  . hcollapse
  . hcliftA (Proxy :: Proxy Consume) (K . consume . unI)
  $ sop
