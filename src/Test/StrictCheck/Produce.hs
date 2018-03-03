module Test.StrictCheck.Produce
  ( Produce(..)
  , recur
  , build
  , returning
  , variadic
  , Lazy(..)
  , freely
  , Input
  , Inputs
  ) where

import Test.QuickCheck
import Test.QuickCheck.Gen.Unsafe

import Data.Monoid ((<>))
import Data.Bifunctor

import Test.StrictCheck.Internal.Inputs
import Test.StrictCheck.Consume
import Test.StrictCheck.Curry
import Generics.SOP

import           Data.List.NonEmpty  ( NonEmpty(..) )
import qualified Data.List.NonEmpty as NE


-------------------------------------------------------
-- The user interface for creating Produce instances --
-------------------------------------------------------

-- TODO: parameterize over destruction pattern?

-- | Produce an arbitrary construction, but using Inputs to drive the
-- implicit destruction of the original input value.
class Produce b where
  produce :: (?inputs::Inputs) => Gen b

theInputs :: (?inputs::Inputs) => [Input]
theInputs = getInputs ?inputs

-- | Given an input-consuming producer, wrap it in an outer layer of input
-- consumption, so that this consumption can be interleaved when the producer is
-- called recursively to generate a subfield of a larger produced datatype.
build :: (?inputs::Inputs) => ((?inputs::Inputs) => Gen a) -> Gen a
build gen = do
  (v, is') <- draws theInputs
  vary v $ let ?inputs = Inputs is' in gen

-- | Destruct some inputs to generate an output. This function handles the
-- interleaving of input destruction with output construction. When producing a
-- data type, it should be called to produce each subfield -- *not* produce
-- itself.
recur :: (Produce a, ?inputs::Inputs) => Gen a
recur = build produce


---------------------------------------
-- How to make random lazy functions --
---------------------------------------

-- NOTE: This instance must be defined in this module, as it has to break the
-- abstraction of the Inputs type. No other instance needs to break this.
-- Incidentally, it also must break Gen's abstraction barrier, because it needs
-- to use promote to make a function.

instance (Consume a, Produce b) => Produce (a -> b) where
  produce = returning produce

-- | Create an input-consuming producer of input-consuming functions, given an
-- input-consuming producer for results of that function.
returning :: (Consume a, ?inputs::Inputs) => ((?inputs::Inputs) => Gen b) -> Gen (a -> b)
returning out =
  promote $ \a ->
    let ?inputs = Inputs (consume a : theInputs)
    in build out

-- | Create an input-consuming producer of input-consuming functions, of any
-- arity. This will usually be used in conjuntion with type application, to
-- specify the type(s) of the argument(s) to the function.
variadic ::
  forall args result. (All Consume args, Curry args, SListI args, ?inputs::Inputs)
         => ((?inputs::Inputs) => Gen result) -> Gen (args ⋯-> result)
variadic out =
  fmap (curryAll @args @_ @(NP I)) . promote $ \args ->
    let ?inputs =
          Inputs . (++ theInputs) $
            hcollapse $ hcliftA (Proxy :: Proxy Consume) (K . consume . unI) args
    in build out


-------------------------------------------------------------------------
-- Random destruction of the original input, as transformed into Input --
-------------------------------------------------------------------------

geometric :: (Enum a, Num a) => Gen a
geometric = oneof [return 0, succ <$> geometric]

pick :: NonEmpty a -> Gen (a, [a])
pick as = do
  index <- choose (0, NE.length as - 1)
  return $ pickAt index as
  where
    pickAt 0 (x :| xs) = (x, xs)
    pickAt n (x :| xs) = (x :) <$> pickAt (n - 1) (NE.fromList xs)

draws :: [Input] -> Gen (Variant, [Input])
draws inputs = do
  second concat <$> (downward [inputs] =<< geometric)
  where
    downward :: [[Input]] -> Int -> Gen (Variant, [[Input]])
    downward levels      0 = return (mempty, levels)
    downward levels budget =
      case levels of
        [          ] -> return (mempty, [])
        [  ] : above -> downward above budget  -- backtrack
        here : above ->
          do (v, below, here') <- draw1 (NE.fromList here)
             (v', levels') <- vary v $ downward (below:here':above) (budget-1)
             return (v <> v', levels')

    draw1 :: NonEmpty Input -> Gen (Variant, [Input], [Input])
    draw1 is = do
      (i, rest) <- pick is
      let (v, inside) = draw i
      return (v, inside, rest)


---------------------------------------------
-- Integration with QuickCheck's Arbitrary --
---------------------------------------------

-- | We hook into QuickCheck's existing Arbitrary infrastructure by using
-- a newtype to differentiate our special way of generating things.
newtype Lazy a = Lazy { runLazy :: a }

instance Produce a => Arbitrary (Lazy a) where
  arbitrary = Lazy <$> freely produce

-- | Actually produce an output, given an input-consuming producer. If a
-- function is to be produced, it will be almost-certainly non-strict.
freely :: ((?inputs::Inputs) => Gen a) -> Gen a
freely p = let ?inputs = Inputs [] in p
