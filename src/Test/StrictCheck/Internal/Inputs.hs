module Test.StrictCheck.Internal.Inputs
  ( Variant(..)
  , Input(..)
  , Inputs(..)
  , draw
  ) where

import Test.QuickCheck

--------------------------------------------------
-- The core user-facing types: Input and Inputs --
--------------------------------------------------

-- | A variant which can be applied to any generator--kept in a newtype to get
-- around lack of impredicativity.
newtype Variant =
  Variant { vary :: forall a. Gen a -> Gen a }

instance Monoid Variant where
  v `mappend` w = Variant $ vary v . vary w
  mempty = Variant id

-- | A tree representing all possible destruction sequences for a value
-- Unfolding the contained urns forces a particular random control path
-- for destructing the datatype.
data Input =
  Input Variant [Input]

-- | A list of inputs given to a function, in abstract form. This lazy structure
-- is evaluated piecewise during the course of producing a function, thus
-- triggering the partial evaluation of the original input to the function.
newtype Inputs = Inputs [Input]

draw :: Input -> (Variant, [Input])
draw (Input v is) = (v, is)
