module Test.StrictCheck.Consume
  ( Input
  , Inputs
  , Consume(..)
  , fields
  , consumeTrivial
  , consumePrimitive
  ) where

import Test.QuickCheck
import qualified Data.Urn as Urn
import Generics.SOP

import Test.StrictCheck.Internal.Inputs


-------------------------------------------------------
-- The user interface for creating Consume instances --
-------------------------------------------------------

-- | Generate a tree of all possible ways to destruct the input value.
class Consume a where
  consume :: a -> Input
  default consume :: GConsume a => a -> Input
  consume = gConsume

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
consumePrimitive :: CoArbitrary a => a -> Input
consumePrimitive !a =
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

type GConsume a = (Generic a, All2 Consume (Code a))

gConsume :: GConsume a => a -> Input
gConsume =
  fields
  . hcollapse
  . hcliftA (Proxy :: Proxy Consume) (K . consume . unI)
  . from
