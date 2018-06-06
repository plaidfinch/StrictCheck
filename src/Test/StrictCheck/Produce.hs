{-| This module defines the 'Produce' typeclass, used for generating random
    values for testing in StrictCheck.

    'Produce' is a strict generalization of "Test.QuickCheck"'s 'Arbitrary'
    typeclass. Paired with 'Consume' (a generalization of 'CoArbitrary') it can
    be used to create random non-strict functions, whose strictness behavior is
    dependent on the values given to them.
-}

module Test.StrictCheck.Produce
  ( Produce(..)
  -- * Tools for writing 'Produce' instances
  , recur
  , build
  -- * Producing non-strict functions
  , returning
  , variadic
  -- * Integration with "Test.QuickCheck"'s @Arbitrary@
  , Lazy(..)
  , freely
  -- * Abstract types representing input to a function
  , Input
  , Inputs
  -- * Useful random distributions for processing @Input@s
  , geometric
  , pick1
  , draws
  ) where

import Test.QuickCheck
import Test.QuickCheck.Gen.Unsafe

import Data.Monoid ((<>))

import Test.StrictCheck.Internal.Inputs
import Test.StrictCheck.Consume
import Test.StrictCheck.Curry
import Generics.SOP

import           Data.List.NonEmpty  ( NonEmpty(..) )
import qualified Data.List.NonEmpty as NE

import Data.Complex


-------------------------------------------------------
-- The user interface for creating Produce instances --
-------------------------------------------------------

-- TODO: parameterize over destruction pattern?

-- | Produce an arbitrary value of type @b@, such that destructing that value
-- incrementally evaluates some input to a function.
--
-- Writing instances of @Produce@ is very similar to writing instances of
-- QuickCheck's 'Arbitrary'. The distinction: when making a recursive call to
-- produce a subfield of a structure, __always__ use 'build' or 'recur', and
-- __never__ a direct call to 'produce' itself. This ensures that the input can
-- potentially be demanded at any step of evaluation of the produced value.
--
-- If, in the course of generating a value of type @b@, you need to generate a
-- random value of some other type, which is /not/ going to be a subpart of the
-- resultant @b@ (e.g. a length or depth), use a direct call to @arbitrary@ or
-- some other generator which does not consume input.
--
-- An example instance of @Produce@:
--
-- > data D a
-- >   = X a
-- >   | Y [Int]
-- >
-- > instance Produce a => Produce (D a) where
-- >   produce =
-- >     oneof [ fmap X recur
-- >           , fmap Y recur
-- >           ]
class Produce b where
  produce :: (?inputs::Inputs) => Gen b

theInputs :: (?inputs::Inputs) => [Input]
theInputs = destruct ?inputs

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
returning
  :: (Consume a, ?inputs::Inputs)
  => ((?inputs::Inputs) => Gen b)
  -> Gen (a -> b)
returning out =
  promote $ \a ->
    let ?inputs = Inputs (consume a : theInputs)
    in build out

-- | Create an input-consuming producer of input-consuming functions, of any
-- arity. This will usually be used in conjuntion with type application, to
-- specify the type(s) of the argument(s) to the function.
variadic ::
  forall args result.
  (All Consume args, Curry args, ?inputs::Inputs)
  => ((?inputs::Inputs) => Gen result)
  -> Gen (args ⋯-> result)
variadic out =
  fmap (curryAll @args @_ @(NP I)) . promote $ \args ->
    let ?inputs =
          Inputs . (++ theInputs) $
            hcollapse $ hcliftA (Proxy @Consume) (K . consume . unI) args
    in build out


-------------------------------------------------------------------------
-- Random destruction of the original input, as transformed into Input --
-------------------------------------------------------------------------

-- | Sample a discrete geometric distribution with expectation 1
geometric :: (Enum a, Num a) => Gen a
geometric =
  oneof [ return 0
        , succ <$> geometric ]

-- | Uniformly choose an element of a list, returning the remainder
--
-- Returns an error if the list is empty.
pick1 :: [a] -> Gen (a, [a])
pick1 as = do
  index <- choose (0, length as - 1)
  return $ pickAt index as
  where
    pickAt :: Int -> [a] -> (a, [a])
    pickAt _ [      ] =
      error "pick1: empty list"
    pickAt n (x : xs)
      | n <= 0
      = (x, xs)
      | otherwise
      = let (p, xs') = pickAt (n - 1) xs
        in (p, x : xs')

-- | Destruct a random subpart of the given 'Input's, returning the 'Variant'
-- corresponding to the combined information harvested during this process, and
-- the remaining "leaves" of the inputs yet to be destructed
--
-- To maximize the likelihood that different random consumption paths through
-- the same value will diverge (desirable when generating functions with
-- interesting strictness), @draws@ destructs the forest of @Input@s as a
-- depth-first random traversal with a budget sampled from a geometric
-- distribution with expectation 1.
draws :: [Input] -> Gen (Variant, [Input])
draws inputs = do
  budget <- geometric
  (variants, levels) <- downFrom [inputs] budget
  return (mconcat variants, concat levels)
  where
    downFrom :: [[Input]] -> Int -> Gen ([Variant], [[Input]])
    downFrom levels budget
      | budget <= 0
      = return ([], levels)
      | otherwise
      = case levels of
          [          ] -> return ([], [])
          [  ] : above -> downFrom above budget  -- backtrack
          here : above -> do
            (v, below, here') <- pickChild here
            vary v $ do
              (path, levels') <- downFrom (below : here' : above) (budget - 1)
              return (v : path, levels')

    pickChild :: [Input] -> Gen (Variant, [Input], [Input])
    pickChild is = do
      (i, rest) <- pick1 is
      let (v, inside) = draw i
      return (v, inside, rest)


---------------------------------------------
-- Integration with QuickCheck's Arbitrary --
---------------------------------------------

-- | We hook into QuickCheck's existing Arbitrary infrastructure by using
-- a newtype to differentiate our special way of generating things.
newtype Lazy a
  = Lazy { runLazy :: a }

instance Produce a => Arbitrary (Lazy a) where
  arbitrary = Lazy <$> freely produce

-- | Actually produce an output, given an input-consuming producer. If a
-- function is to be produced, it will be almost-certainly non-strict.
freely :: ((?inputs::Inputs) => Gen a) -> Gen a
freely p = let ?inputs = Inputs [] in p


---------------
-- Instances --
---------------

instance Produce ()       where produce = arbitrary
instance Produce Bool     where produce = arbitrary
instance Produce Ordering where produce = arbitrary

instance Produce Char     where produce = arbitrary
instance Produce Word     where produce = arbitrary
instance Produce Int      where produce = arbitrary
instance Produce Double   where produce = arbitrary
instance Produce Float    where produce = arbitrary
instance Produce Rational where produce = arbitrary
instance Produce Integer  where produce = arbitrary

instance (Arbitrary a, RealFloat a) => Produce (Complex a) where
  produce = arbitrary

instance Produce a => Produce (Maybe a) where
  produce =
    oneof [ return Nothing
          , Just <$> recur
          ]

instance (Produce a, Produce b) => Produce (Either a b) where
  produce =
    oneof [ Left <$> recur
          , Right <$> recur
          ]

instance (Produce a) => Produce [a] where
  produce =
    frequency [ (1, return [])
              , (1, (:) <$> recur
                        <*> recur)
              ]
