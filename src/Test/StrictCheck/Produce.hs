module Test.StrictCheck.Produce
  ( Produce(..)
  , recur
  , producePrimitive
  , producing
  , returning
  , variadic
  , Lazy(..)
  , freely
  , Input
  , Inputs
  ) where

import Test.QuickCheck
import Test.QuickCheck.Gen.Unsafe

import           Data.Urn ( Urn )
import qualified Data.Urn          as Urn
import qualified Data.Urn.Internal as Urn ( uninsert )

import Data.Monoid ((<>))
import Control.Monad

import Test.StrictCheck.Internal.Inputs
import Test.StrictCheck.Consume

import Test.StrictCheck.Curry
import Test.StrictCheck.Curry.Function
import Generics.SOP


-------------------------------------------------------
-- The user interface for creating Produce instances --
-------------------------------------------------------

-- | Produce an arbitrary construction, but using Inputs to drive the
-- implicit destruction of the original input value.
class Produce b where
  produce :: Inputs -> Gen b

-- | Given an input-consuming producer, wrap it in an outer layer of input
-- consumption, so that this consumption can be interleaved when the producer is
-- called recursively to generate a subfield of a larger produced datatype.
producing :: (Inputs -> Gen a) -> Inputs -> Gen a
producing part (Inputs is) = do
  (v, is') <- draws is
  vary v $ part (Inputs is')

-- | Destruct some inputs to generate an output. This function handles the
-- interleaving of input destruction with output construction. When producing a
-- data type, it should be called to produce each subfield -- *not* produce
-- itself.
recur :: Produce a => Inputs -> Gen a
recur = producing produce

-- | Use the Arbitrary instance for a type to produce it. This should only be
-- used for "flat" types, i.e. those which contain no interesting substructure.
producePrimitive :: Arbitrary b => Inputs -> Gen b
producePrimitive _ = arbitrary


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
returning :: Consume a => (Inputs -> Gen b) -> Inputs -> Gen (a -> b)
returning out =
  \(Inputs inputs) ->
    promote $ \a ->
      producing out (Inputs (consume a : inputs))

-- | Create an input-consuming producer of input-consuming functions, of any
-- arity. This will usually be used in conjuntion with type application, to
-- specify the type(s) of the argument(s) to the function.
variadic ::
  forall args result. (All Consume args, Curry args result, SListI args)
         => (Inputs -> Gen result) -> Inputs -> Gen (args ⋯-> result)
variadic out =
  \(Inputs inputs) ->
    fmap (curryFunction @args . toFunction) . promote $ \args ->
      producing out . Inputs . (++ inputs) $
        hcollapse $ hcliftA (Proxy :: Proxy Consume) (K . consume . unI) args


-------------------------------------------------------------------------
-- Random destruction of the original input, as transformed into Input --
-------------------------------------------------------------------------

-- | Pattern-match on a randomly chosen single constructor of the input, and
-- produce the corresponding Variant, whose value depends on which constructor
-- was matched.
draw :: Input -> Gen (Variant, [Input])
draw (Input i) =
  case i of
    Nothing  -> return mempty
    Just urn -> do
      (_, (v, Input inner), outer) <- Urn.remove urn
      let (vs, is) = unzip $ maybe [] contents inner
      return $ (v <> mconcat vs, Input outer : is)
  where
    contents :: Urn a -> [a]
    contents urn =
      case Urn.uninsert urn of
        (_, a, _, Just urn') -> a : contents urn'
        (_, a, _, Nothing)   -> [a]

-- | Destruct some randomly chosen subparts of the input, and return a composite
-- Variant whose entropy is derived from all the inputs destructed. The
-- probability of n pieces of input being consumed decreases as n increases.
draws :: [Input] -> Gen (Variant, [Input])
draws inputs =
  fmap mconcat . forM inputs $ \input -> do
    frequency [ (1,) $ return (mempty, [input])
              , (1,) $ do
                  (v,  is)  <- draw input
                  (v', is') <- vary v $ draws is
                  return (v <> v', is')
              ]

-- TODO: Allow the user to tune how biased towards strictness things are?
-- What should the default be?


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
freely :: (Inputs -> Gen a) -> Gen a
freely p = p (Inputs [])
