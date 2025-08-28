{-| This module defines the 'Consume' typeclass, used for incrementally
    destructing inputs to random non-strict functions.

    Calling 'consume' on some value lazily returns an abstract type of 'Input',
    which contains all the entropy present in the original value. Paired with
    'Test.StrictCheck.Produce', these @Input@ values can be used to generate
    random non-strict functions, whose strictness behavior is dependent on the
    values given to them.
-}
module Test.StrictCheck.Consume
  ( -- * Incrementally consuming input
    Input
  , Inputs
  , Consume(..)
  -- * Manually writing 'Consume' instances
  , constructor
  , normalize
  , consumeTrivial
  , consumePrimitive
  -- * Generically deriving 'Consume' instances
  , GConsume
  , gConsume
  ) where

import Test.QuickCheck
import Generics.SOP
import Generics.SOP.NS

import Test.StrictCheck.Internal.Inputs

import Data.Complex

import Data.Foldable as Fold
import Data.List.NonEmpty (NonEmpty(..))
import Data.Tree     as Tree
import Data.Set      as Set
import Data.Map      as Map
import Data.Sequence as Seq
import Data.IntMap   as IntMap
import Data.IntSet   as IntSet


-- | Lazily monomorphize some input value, by converting it into an @Input@.
-- This is an incremental version of QuickCheck's @CoArbitrary@ typeclass.
-- It can also be seen as a generalization of the @NFData@ class.
--
-- Instances of @Consume@ can be derived automatically for any type implementing
-- the @Generic@ class from "GHC.Generics". Using the @DeriveAnyClass@
-- extension, we can say:
--
-- > import GHC.Generics as GHC
-- > import Generics.SOP as SOP
-- >
-- > data D x y
-- >   = A
-- >   | B (x, y)
-- >   deriving (GHC.Generic, SOP.Generic, Consume)
--
-- This automatic derivation follows these rules, which you can follow too if
-- you're manually writing an instance for some type which is not @Generic@:
--
-- For each distinct constructor, make a single call to 'constructor' with
-- a distinct @Int@, and a list of @Input@s, each created by recursively calling
-- 'consume' on every field in that constructor. For abstract types (e.g. sets),
-- the same procedure can be used upon an extracted list representation of the
-- contents.
class Consume a where
  -- | Convert an @a@ into an @Input@ by recursively destructing it using calls
  -- to @consume@
  consume :: a -> Input
  default consume :: GConsume a => a -> Input
  consume = gConsume

-- | Reassemble pieces of input into a larger Input: this is to be called on the
-- result of @consume@-ing subparts of input
constructor :: Int -> [Input] -> Input
constructor n !is =
  Input (Variant (variant n)) is

-- | Use the CoArbitrary instance for a type to consume it
--
-- This should only be used for "flat" types, i.e. those which contain no
-- interesting consumable substructure, as it's fully strict (non-incremental)
consumePrimitive :: CoArbitrary a => a -> Input
consumePrimitive !a =
  Input (Variant (coarbitrary a)) []

-- | Consume a type which has no observable structure whatsoever
--
-- This should only be used for types for which there is only one inhabitant, or
-- for which inhabitants cannot be distinguished at all.
consumeTrivial :: a -> Input
consumeTrivial !_ =
  Input mempty []

-- | Fully normalize something which can be consumed
normalize :: Consume a => a -> ()
normalize (consume -> input) = go input
  where
    go (Input _ is) = Fold.foldr seq () (fmap go is)

--------------------------------------------
-- Deriving Consume instances generically --
--------------------------------------------

-- | The constraints necessary to generically @consume@ something
type GConsume a = (Generic a, All2 Consume (Code a))

-- | Generic 'consume'
gConsume :: GConsume a => a -> Input
gConsume !(from -> sop) =
  constructor (index_SOP sop)
  . hcollapse
  . hcliftA (Proxy @Consume) (K . consume . unI)
  $ sop


---------------
-- Instances --
---------------

instance Consume (a -> b)  where consume = consumeTrivial
instance Consume (Proxy p) where consume = consumeTrivial

instance Consume Char     where consume = consumePrimitive
instance Consume Word     where consume = consumePrimitive
instance Consume Int      where consume = consumePrimitive
instance Consume Double   where consume = consumePrimitive
instance Consume Float    where consume = consumePrimitive
instance Consume Rational where consume = consumePrimitive
instance Consume Integer  where consume = consumePrimitive
instance CoArbitrary a => Consume (Complex a) where
  consume = consumePrimitive

instance Consume ()
instance Consume Bool
instance Consume Ordering
instance Consume a => Consume (Maybe a)
instance (Consume a, Consume b) => Consume (Either a b)
instance Consume a => Consume [a]


instance Consume a => Consume (NonEmpty a) where
  consume (a :| as) = constructor 0 [consume a, consume as]

instance Consume a => Consume (Tree a) where
  consume (Node a as) = constructor 0 [consume a, consume as]

instance Consume v => Consume (Map k v) where
  consume = constructor 0 . fmap (consume . snd) . Map.toList

consumeContainer :: (Consume a, Foldable t) => t a -> Input
consumeContainer = constructor 0 . fmap consume . Fold.toList

instance Consume v => Consume (Seq v)    where consume = consumeContainer
instance Consume v => Consume (Set v)    where consume = consumeContainer
instance Consume v => Consume (IntMap v) where consume = consumeContainer
instance Consume IntSet where
  consume = consumeContainer . IntSet.toList

-- TODO: instances for the rest of Containers

instance (Consume a, Consume b) => Consume (a, b)
instance (Consume a, Consume b, Consume c) => Consume (a, b, c)
instance (Consume a, Consume b, Consume c, Consume d) => Consume (a, b, c, d)
instance ( Consume a, Consume b, Consume c, Consume d, Consume e
         ) => Consume
  (a, b, c, d, e)
instance ( Consume a, Consume b, Consume c, Consume d, Consume e, Consume f
         ) => Consume
  (a, b, c, d, e, f)
instance ( Consume a, Consume b, Consume c, Consume d, Consume e, Consume f
         , Consume g
         ) => Consume
  (a, b, c, d, e, f, g)
instance ( Consume a, Consume b, Consume c, Consume d, Consume e, Consume f
         , Consume g, Consume h
         ) => Consume
  (a, b, c, d, e, f, g, h)
instance ( Consume a, Consume b, Consume c, Consume d, Consume e, Consume f
         , Consume g, Consume h, Consume i
         ) => Consume
  (a, b, c, d, e, f, g, h, i)
instance ( Consume a, Consume b, Consume c, Consume d, Consume e, Consume f
         , Consume g, Consume h, Consume i, Consume j
         ) => Consume
  (a, b, c, d, e, f, g, h, i, j)
instance ( Consume a, Consume b, Consume c, Consume d, Consume e, Consume f
         , Consume g, Consume h, Consume i, Consume j, Consume k
         ) => Consume
  (a, b, c, d, e, f, g, h, i, j, k)
instance ( Consume a, Consume b, Consume c, Consume d, Consume e, Consume f
         , Consume g, Consume h, Consume i, Consume j, Consume k, Consume l
         ) => Consume
  (a, b, c, d, e, f, g, h, i, j, k, l)
instance ( Consume a, Consume b, Consume c, Consume d, Consume e, Consume f
         , Consume g, Consume h, Consume i, Consume j, Consume k, Consume l
         , Consume m
         ) => Consume
  (a, b, c, d, e, f, g, h, i, j, k, l, m)
instance ( Consume a, Consume b, Consume c, Consume d, Consume e, Consume f
         , Consume g, Consume h, Consume i, Consume j, Consume k, Consume l
         , Consume m, Consume n
         ) => Consume
  (a, b, c, d, e, f, g, h, i, j, k, l, m, n)
instance ( Consume a, Consume b, Consume c, Consume d, Consume e, Consume f
         , Consume g, Consume h, Consume i, Consume j, Consume k, Consume l
         , Consume m, Consume n, Consume o
         ) => Consume
  (a, b, c, d, e, f, g, h, i, j, k, l, m, n, o)
instance ( Consume a, Consume b, Consume c, Consume d, Consume e, Consume f
         , Consume g, Consume h, Consume i, Consume j, Consume k, Consume l
         , Consume m, Consume n, Consume o, Consume p
         ) => Consume
  (a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p)
instance ( Consume a, Consume b, Consume c, Consume d, Consume e, Consume f
         , Consume g, Consume h, Consume i, Consume j, Consume k, Consume l
         , Consume m, Consume n, Consume o, Consume p, Consume q
         ) => Consume
  (a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q)
instance ( Consume a, Consume b, Consume c, Consume d, Consume e, Consume f
         , Consume g, Consume h, Consume i, Consume j, Consume k, Consume l
         , Consume m, Consume n, Consume o, Consume p, Consume q, Consume r
         ) => Consume
  (a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r)
instance ( Consume a, Consume b, Consume c, Consume d, Consume e, Consume f
         , Consume g, Consume h, Consume i, Consume j, Consume k, Consume l
         , Consume m, Consume n, Consume o, Consume p, Consume q, Consume r
         , Consume s
         ) => Consume
  (a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s)
instance ( Consume a, Consume b, Consume c, Consume d, Consume e, Consume f
         , Consume g, Consume h, Consume i, Consume j, Consume k, Consume l
         , Consume m, Consume n, Consume o, Consume p, Consume q, Consume r
         , Consume s, Consume t
         ) => Consume
  (a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t)
instance ( Consume a, Consume b, Consume c, Consume d, Consume e, Consume f
         , Consume g, Consume h, Consume i, Consume j, Consume k, Consume l
         , Consume m, Consume n, Consume o, Consume p, Consume q, Consume r
         , Consume s, Consume t, Consume u
         ) => Consume
  (a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u)
instance ( Consume a, Consume b, Consume c, Consume d, Consume e, Consume f
         , Consume g, Consume h, Consume i, Consume j, Consume k, Consume l
         , Consume m, Consume n, Consume o, Consume p, Consume q, Consume r
         , Consume s, Consume t, Consume u, Consume v
         ) => Consume
  (a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v)
instance ( Consume a, Consume b, Consume c, Consume d, Consume e, Consume f
         , Consume g, Consume h, Consume i, Consume j, Consume k, Consume l
         , Consume m, Consume n, Consume o, Consume p, Consume q, Consume r
         , Consume s, Consume t, Consume u, Consume v, Consume w
         ) => Consume
  (a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w)
instance ( Consume a, Consume b, Consume c, Consume d, Consume e, Consume f
         , Consume g, Consume h, Consume i, Consume j, Consume k, Consume l
         , Consume m, Consume n, Consume o, Consume p, Consume q, Consume r
         , Consume s, Consume t, Consume u, Consume v, Consume w, Consume x
          ) => Consume
  (a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x)
instance ( Consume a, Consume b, Consume c, Consume d, Consume e, Consume f
         , Consume g, Consume h, Consume i, Consume j, Consume k, Consume l
         , Consume m, Consume n, Consume o, Consume p, Consume q, Consume r
         , Consume s, Consume t, Consume u, Consume v, Consume w, Consume x
         , Consume y
         ) => Consume
  (a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y)
instance ( Consume a, Consume b, Consume c, Consume d, Consume e, Consume f
         , Consume g, Consume h, Consume i, Consume j, Consume k, Consume l
         , Consume m, Consume n, Consume o, Consume p, Consume q, Consume r
         , Consume s, Consume t, Consume u, Consume v, Consume w, Consume x
         , Consume y, Consume z
         ) => Consume
  (a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z)
