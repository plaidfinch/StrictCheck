
{-# LANGUAGE ScopedTypeVariables, LambdaCase, BangPatterns, TupleSections,
  RankNTypes #-}

{-# OPTIONS_GHC -fno-warn-type-defaults #-}

module FixGen where

import Test.QuickCheck
import Test.QuickCheck.Gen.Unsafe (promote)
import Data.Urn as Urn hiding (frequency)
import Data.Urn.Internal as Urn (uninsert)
import Data.Function
import Control.Category ((>>>))

import Continuations

-- A tree representing all possible destruction sequences for a value
-- If constructed lazily, unfolding the contained urns forces a particular
-- random control path destructing the datatype
newtype Cases =
  Cases { cases :: Maybe (Urn (Variant, Cases)) }

-- A variant which can be applied to any generator--kept in a newtype to get
-- around lack of impredicativity
newtype Variant =
  Variant { vary :: forall a. Gen a -> Gen a }

-- A nested sequence of generators, each of which when run destructs some part
-- of the input it's secretly closed over
data Variants =
  Variants { pull :: Gen (Variant, Variants) }

-- Generates a tree of all possible ways to destruct the input
class Consume a where
  consume :: a -> Cases

-- Produces an arbitrary construction, but using a Variants to drive the
-- implicit destruction of the input
class Produce b where
  produce :: Variants -> Gen b

-- This converts a tree of all possible case matches into a concrete series of
-- infinitely nested generators, which represent a particular arbitrary
-- destruction of the input closed overy by the Cases
variants :: Cases -> Variants
variants original@(Cases cs) = cs & \case
  Nothing  -> idVariants
  Just urn ->
    Variants $ do
      (_, (v, Cases inner), outer) <- Urn.remove urn
      fmap (v,) . stutter $
        case (inner, outer) of
          (Nothing, Nothing)          -> idVariants
          (Nothing, Just outside)     -> variants (Cases (Just outside))
          (Just inside, Nothing)      -> variants (Cases (Just inside))
          (Just inside, Just outside) ->
            variants . Cases . Just $
              addToUrn outside (contents inside)
  where
    idVariants :: Variants
    idVariants = fix $ \rest ->
      Variants $ return (Variant (variant 0), rest)

    stutter :: Variants -> Gen Variants
    stutter r =
      frequency [ (1, return $ variants original)
                , (2, return r)
                , (3, return $ twice r) ]

    twice :: Variants -> Variants
    twice r = Variants $ do
      (v, rest) <- pull r
      (v', rest') <- pull rest
      return (Variant (vary v' . vary v), rest')

    contents :: Urn a -> [(Weight, a)]
    contents urn =
      case uninsert urn of
        (weight, a, _, Just urn') -> (weight, a) : contents urn'
        (weight, a, _, Nothing)   -> [(weight, a)]

-- A generator for a partially lazy function
lazyFunction :: (Consume a, Produce b) => Gen (a -> b)
lazyFunction =
  promote (consume >>> variants >>> produce)


-- Helpers for writing Consume and Produce instances...

-- If something is opaque and all we know is that it can be reduced to whnf,
-- this default consumer should be used
consumeAtomic :: a -> Cases
consumeAtomic !_ = fields []

-- If something is opaque and all we know is how to generate an arbitrary one,
-- we can fall back on its Arbitrary instance
produceAtomic :: Arbitrary b => Variants -> Gen b
produceAtomic _ = arbitrary

-- Always use this to destruct the fields of a product. It makes sure that you
-- get unique variants embedded in the Cases... and there is absolutely no
-- reason not to use it.
fields :: [(Integer, Cases)] -> Cases
fields =
  Cases . Urn.fromList . map (1,) .
  map (\(i, cs) -> (Variant (variant i), cs))

-- Always use this (on the passed "continuation") to construct the fields of a
-- product. It makes sure that each time you produce some output, you have the
-- possibility of consuming more input, as well as guaranteeing that the entropy
-- from the input can be used to randomize the output.
recur :: Produce a => Variants -> Gen a
recur k = do
  (v, rest) <- pull k
  vary v (produce rest)


-- Some instances!

instance Produce Integer where
  produce = produceAtomic

instance Consume Integer where
  consume = consumeAtomic

instance (Produce a, Produce b) => Produce (a, b) where
  produce k =
    (,) <$> recur k <*> recur k

instance (Consume a, Consume b) => Consume (a, b) where
  consume (x, y) =
    fields [ (1, consume x)
           , (1, consume y) ]

instance Produce Nat where
  produce k = do
    frequency [ (1, return Z)
              , (2, S <$> recur k)
              ]

instance Consume Nat where
  consume Z     = fields []
  consume (S n) = fields [ (1, consume n) ]

instance (Produce a) => Produce [a] where
  produce k = do
    frequency [ (1, return [])
              , (4, (:) <$> recur k
                        <*> recur k)
              ]

instance (Consume a) => Consume [a] where
  consume = \case
    []       -> fields []
    (x : xs) -> fields [ (1, consume x)
                       , (1, consume xs)
                       ]
