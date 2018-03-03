module Test.StrictCheck.Consume
  ( Input
  , Inputs
  , Consume(..)
  , constructor
  , normalize
  , consumeTrivial
  , consumePrimitive
  ) where

import Test.QuickCheck
import Generics.SOP
import Generics.SOP.NS

import Test.StrictCheck.Internal.Inputs

import Data.Monoid    as Monoid
import Data.Semigroup as Semigroup
import Control.Applicative
import Control.Monad.State
import Control.Monad.Cont
import Control.Monad.Except
import Control.Monad.Identity
import Control.Monad.RWS
import Control.Monad.Reader
import Control.Monad.Writer
import Control.Monad.ST
import GHC.Conc
import Data.Functor.Product as Functor
import Data.Functor.Sum     as Functor
import Data.Functor.Compose as Functor
import Data.Complex

import Data.Foldable as Fold
import Data.List.NonEmpty (NonEmpty(..))
import Data.Tree     as Tree
import Data.Set      as Set
import Data.Map      as Map
import Data.Sequence as Seq
import Data.IntMap   as IntMap
import Data.IntSet   as IntSet


-------------------------------------------------------
-- The user interface for creating Consume instances --
-------------------------------------------------------

-- | Generate a tree of all possible ways to destruct the input value.
class Consume a where
  consume :: a -> Input
  default consume :: GConsume a => a -> Input
  consume = gConsume

-- | Reassemble pieces of input into a larger Input.
constructor :: Int -> [Input] -> Input
constructor n !is =
  Input (Variant (variant n)) is

-- | Use the CoArbitrary instance for a type to consume it. This should only be
-- used for "flat" types, i.e. those which contain no interesting substructure.
consumePrimitive :: CoArbitrary a => a -> Input
consumePrimitive !a =
  Input (Variant (coarbitrary a)) []

-- | If a type has no observable properties or substructure which can be used
-- to drive the randomization of output, consumption should merely evaluate a
-- value to weak-head normal form.
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

type GConsume a = (Generic a, All2 Consume (Code a))

gConsume :: GConsume a => a -> Input
gConsume !(from -> sop) =
  constructor (index_SOP sop)
  . hcollapse
  . hcliftA (Proxy :: Proxy Consume) (K . consume . unI)
  $ sop


---------------
-- Instances --
---------------

instance Consume (IO a)    where consume = consumeTrivial
instance Consume (STM a)   where consume = consumeTrivial
instance Consume (ST s a)  where consume = consumeTrivial
instance Consume (a -> b)  where consume = consumeTrivial
instance Consume (Proxy p) where consume = consumeTrivial

instance Consume Char     where consume = consumePrimitive
instance Consume Word     where consume = consumePrimitive
instance Consume Int      where consume = consumePrimitive
instance Consume Double   where consume = consumePrimitive
instance Consume Float    where consume = consumePrimitive
instance Consume Rational where consume = consumePrimitive
instance Consume Integer  where consume = consumePrimitive
instance (CoArbitrary a, RealFloat a) => Consume (Complex a) where
  consume = consumePrimitive

deriving newtype instance Consume a => Consume (Identity a)
deriving newtype instance Consume (RWST r w s m a)
deriving newtype instance Consume (ReaderT r m a)
deriving newtype instance Consume (StateT s m a)
deriving newtype instance Consume (m (a, w)) => Consume (WriterT w m a)
deriving newtype instance Consume (ContT r m a)
deriving newtype instance Consume (m (Either e a)) => Consume (ExceptT e m a)
deriving newtype instance Consume a => Consume (ZipList a)
deriving newtype instance Consume a => Consume (Monoid.First a)
deriving newtype instance Consume a => Consume (Monoid.Last a)
deriving newtype instance Consume a => Consume (Semigroup.First a)
deriving newtype instance Consume a => Consume (Semigroup.Last a)
deriving newtype instance Consume a => Consume (Min a)
deriving newtype instance Consume a => Consume (Max a)
deriving newtype instance Consume a => Consume (Monoid.Sum a)
deriving newtype instance Consume a => Consume (Monoid.Product a)
deriving newtype instance Consume (f (g a)) => Consume (Functor.Compose f g a)
deriving newtype instance Consume a => Consume (Dual a)
deriving newtype instance Consume a => Consume (Const a b)

instance Consume ()
instance Consume Bool
instance Consume Ordering
instance Consume a => Consume (Maybe a)
instance (Consume a, Consume b) => Consume (Either a b)
instance Consume a => Consume [a]

deriving newtype instance Consume a => Consume (I a)
deriving newtype instance Consume a => Consume (K a b)
-- TODO: instances for the rest of the SOP newtypes

instance (Consume (f a), Consume (g a)) => Consume (Functor.Sum f g a) where
  consume (InL a) = constructor 0 [consume a]
  consume (InR b) = constructor 1 [consume b]

instance (Consume (f a), Consume (g a)) => Consume (Functor.Product f g a) where
  consume (Pair a b) = constructor 0 [consume a, consume b]

instance (Consume a, Consume b) => Consume (Semigroup.Arg a b) where
  consume (Arg a b) = constructor 0 [consume a, consume b]

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
instance Consume v => Consume IntSet where
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
