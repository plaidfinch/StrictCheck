{-| __Internal module__: This module does not make any stability guarantees, and
    may not adhere to the PVP.

    This module implements the rose-tree data structure used by StrictCheck to
    monomorphize inputs to functions. We decouple the consumption of input from
    the production of output by converting any input to an @Input@: a lazily
    constructed rose tree with nodes each containing a @(Gen a -> Gen a)@ which
    captures a random perturbation associated with the shape of the value
    consumed. The tree-shape of an @Input@ matches that of the entire consumed
    value, and evaluating any subpart of it forces the evaluation of the
    corresponding part of the original value.
-}
module Test.StrictCheck.Internal.Inputs
  ( Variant(..)
  , Input(..)
  , Inputs(..)
  , draw
  , destruct
  ) where

import Test.QuickCheck (Gen)


--------------------------------------------------
-- The core user-facing types: Input and Inputs --
--------------------------------------------------

-- | A variant which can be applied to any generator--kept in a newtype to get
-- around lack of impredicativity.
newtype Variant
  = Variant { vary :: forall a. Gen a -> Gen a }

instance Semigroup Variant where
  v <> w = Variant (vary v . vary w)

instance Monoid Variant where
  mappend = (<>)
  mempty = Variant id

-- | A tree representing all possible destruction sequences for a value
-- Unfolding the contained lists forces a particular random control path
-- for destructing the datatype.
data Input
  = Input Variant [Input]  -- ^ Not exposed in safe API

-- | A list of inputs given to a function, in abstract form. This lazy structure
-- is evaluated piecewise during the course of producing a function, thus
-- triggering the partial evaluation of the original input to the function.
newtype Inputs
  = Inputs [Input]  -- ^ Not exposed in safe API

-- | Extract the list of @Input@s from an @Inputs@
destruct :: Inputs -> [Input]
destruct (Inputs is) = is

-- | Extract the entropy and subfield-@Input@s from a given @Input@
draw :: Input -> (Variant, [Input])
draw (Input v is) = (v, is)
