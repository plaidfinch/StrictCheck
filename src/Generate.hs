
{-# LANGUAGE ScopedTypeVariables, LambdaCase, BangPatterns, TupleSections,
  RankNTypes, ViewPatterns #-}

{-# OPTIONS_GHC -fno-warn-type-defaults #-}

module Generate ( Cases
                , Inputs
                , Consume(..)
                , Produce(..)
                , Lazy(..)
                , lazy
                , fields
                , recur
                , input
                , consumeAtomic
                , produceAtomic
                ) where

import Test.QuickCheck
import Test.QuickCheck.Gen.Unsafe (promote)
import Data.Urn as Urn hiding (frequency)
import Data.Urn.Internal as Urn (uninsert)
import Data.Function (fix, (&))
import Data.Monoid
import Control.Monad

-- A tree representing all possible destruction sequences for a value
-- If constructed lazily, unfolding the contained urns forces a particular
-- random control path destructing the datatype
newtype Cases =
  Cases (Maybe (Urn (Variant, Cases)))

-- A variant which can be applied to any generator--kept in a newtype to get
-- around lack of impredicativity
newtype Variant =
  Variant { vary :: forall a. Gen a -> Gen a }

instance Monoid Variant where
  v `mappend` w = Variant $ vary v . vary w
  mempty = Variant id

-- A nested sequence of generators, each of which when run destructs some part
-- of the input it's secretly closed over
data Variants =
  Variants { pull :: Gen (Variant, Variants) }

-- A list of some number of Variants'es, each corresponding to the destruction
-- of a single input to a potentially many-argument function
newtype Inputs = Inputs [Variants]

instance Monoid Inputs where
  Inputs vs `mappend` Inputs ws = Inputs $ vs ++ ws
  mempty = Inputs []

-- Generates a tree of all possible ways to destruct the input
class Consume a where
  consume :: a -> Cases

-- Produces an arbitrary construction, but using a Variants to drive the
-- implicit destruction of the input
class Produce b where
  produce :: Inputs -> Gen b

-- This converts a tree of all possible case matches into a concrete series of
-- infinitely nested generators, which represent a particular arbitrary
-- destruction of the input closed overy by the Cases
variants :: Cases -> Variants
variants (Cases cs) = cs & \case
  Nothing  -> identityVariants
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

identityVariants :: Variants
identityVariants = fix $ \vs ->
  Variants $ return (mempty, vs)


-- The user interface for writing Produce and Consume instances:

input :: Cases -> Inputs
input cs = Inputs [variants cs]

recur :: Produce a => Inputs -> Gen a
recur (Inputs vss) = do
  (vs, vss') <- unzip <$> mapM (pull <=< stutter) vss
  vary (mconcat vs) $ produce (Inputs vss')
  where
    stutter :: Variants -> Gen Variants
    stutter vs = do
      frequency [ (1, return $ delay vs)
                , (1, repeatedly more vs) ]

    repeatedly :: (a -> a) -> a -> Gen a
    repeatedly f a =
      frequency [ (2, return a)
                , (1, f <$> repeatedly f a) ]

    delay :: Variants -> Variants
    delay vs = Variants $
      return (mempty, vs)

    more :: Variants -> Variants
    more vs = Variants $ do
      (v,  vs')  <- pull vs
      (v', vs'') <- pull vs'
      return (v <> v', vs'')

-- If something is opaque and all we know is that it can be reduced to whnf,
-- this default consumer should be used
consumeAtomic :: a -> Cases
consumeAtomic !_ = fields []

-- If something is opaque and all we know is how to generate an arbitrary one,
-- we can fall back on its Arbitrary instance
produceAtomic :: Arbitrary b => Inputs -> Gen b
produceAtomic _ = arbitrary

-- Always use this to destruct the fields of a product. It makes sure that you
-- get unique variants embedded in the Cases... and there is absolutely no
-- reason not to use it.
fields :: [(Word, Cases)] -> Cases
fields =
  Cases . Urn.fromList .
    zipWith (\v (weight, cases) ->
               (weight, (Variant (variant v), cases))) [1..]

-- We can hook into QuickCheck's existing Arbitrary infrastructure by using
-- a newtype to differentiate our way of generating things.
newtype Lazy a = Lazy { runLazy :: a }

instance Produce a => Arbitrary (Lazy a) where
  arbitrary = Lazy <$> produce mempty

lazy :: Produce a => Gen a
lazy = runLazy <$> arbitrary

-- Some instances!

-- The most important instance!
-- NOTE: you may be tempted to call produce instead of recur here, but this will
-- mean that all of your functions will be 1st-output-lazy. Thus, we use recur.
instance (Consume a, Produce b) => Produce (a -> b) where
  produce inputs =
    promote $ \a ->
      recur (input (consume a) <> inputs)

instance Produce Integer where
  produce = produceAtomic

instance Consume Integer where
  consume = consumeAtomic

instance (Produce a, Produce b) => Produce (a, b) where
  produce inputs =
    (,) <$> recur inputs <*> recur inputs

instance (Consume a, Consume b) => Consume (a, b) where
  consume (x, y) =
    fields [ (1, consume x)
           , (1, consume y) ]

instance (Produce a) => Produce [a] where
  produce inputs = do
    frequency [ (1, return [])
              , (4, (:) <$> recur inputs
                        <*> recur inputs)
              ]

instance (Consume a) => Consume [a] where
  consume []       = fields []
  consume (x : xs) = fields [ (1, consume x)
                            , (1, consume xs)
                            ]
