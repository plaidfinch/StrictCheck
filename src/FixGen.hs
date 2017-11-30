
{-# LANGUAGE ScopedTypeVariables, LambdaCase, BangPatterns, TupleSections,
  RankNTypes #-}

{-# OPTIONS_GHC -fno-warn-type-defaults #-}

module FixGen ( Cases
              , Consume(..)
              , Produce(..)
              , lazyFunction
              , consumeAtomic
              , produceAtomic
              , fields
              ) where

import Test.QuickCheck
import Test.QuickCheck.Gen.Unsafe (promote)
import Data.Urn as Urn hiding (frequency)
import Data.Urn.Internal as Urn (uninsert)
import Data.Function
import Control.Category ((>>>))

-- A tree representing all possible destruction sequences for a value
-- If constructed lazily, unfolding the contained urns forces a particular
-- random control path destructing the datatype
newtype Cases =
  Cases (Maybe (Urn (Variant, Cases)))

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
  produce :: (forall a. Produce a => Gen a) -> Gen b

-- This converts a tree of all possible case matches into a concrete series of
-- infinitely nested generators, which represent a particular arbitrary
-- destruction of the input closed overy by the Cases
variants :: Cases -> Variants
variants (Cases cs) = cs & \case
  Nothing  -> fix delay
  Just urn ->
    Variants $ do
      (_, (v, Cases inner), outer) <- Urn.remove urn
      return $ (v,) $ variants $ Cases $ merge inner outer
  where
    merge :: Maybe (Urn a) -> Maybe (Urn a) -> Maybe (Urn a)
    merge left right =
      case (left, right) of
        (Nothing, Nothing) -> Nothing
        (Nothing, Just r)  -> Just r
        (Just l, Nothing)  -> Just l
        (Just l, Just r)   -> Just $ addToUrn l (contents r)

    contents :: Urn a -> [(Weight, a)]
    contents urn =
      case uninsert urn of
        (weight, a, _, Just urn') -> (weight, a) : contents urn'
        (weight, a, _, Nothing)   -> [(weight, a)]

-- Make a recursive produce generator that threads through
interleave :: Produce a => Variants -> Gen a
interleave vs = do
  (v, vs') <- pull =<< stutter vs
  vary v (produce (interleave vs'))

stutter :: Variants -> Gen Variants
stutter vs = do
  frequency [ (2, return $ delay vs)
            , (2, repeatedly more vs) ]

repeatedly :: (a -> a) -> a -> Gen a
repeatedly f a =
  frequency [ (2, return a)
            , (1, f <$> repeatedly f a) ]

delay :: Variants -> Variants
delay vs = Variants $
  return (Variant (variant 0), vs)

more :: Variants -> Variants
more vs = Variants $ do
  (v, vs') <- pull vs
  (v', vs'') <- pull vs'
  return (Variant (vary v' . vary v), vs'')


-- A generator for a partially lazy function
-- TODO: Make this respect the size parameter (should limit both size of
-- produced values and maximum continuity of function)
lazyFunction :: (Consume a, Produce b) => Gen (a -> b)
lazyFunction = promote (consume >>> variants >>> interleave)


-- Helpers for writing Consume and Produce instances...

-- If something is opaque and all we know is that it can be reduced to whnf,
-- this default consumer should be used
consumeAtomic :: a -> Cases
consumeAtomic !_ = fields []

-- If something is opaque and all we know is how to generate an arbitrary one,
-- we can fall back on its Arbitrary instance
produceAtomic :: Arbitrary b => (forall a. Produce a => Gen a) -> Gen b
produceAtomic _ = arbitrary

-- Always use this to destruct the fields of a product. It makes sure that you
-- get unique variants embedded in the Cases... and there is absolutely no
-- reason not to use it.
fields :: [(Word, Cases)] -> Cases
fields =
  Cases . Urn.fromList .
    zipWith (\v (weight, cases) ->
               (weight, (Variant (variant v), cases))) [1..]
