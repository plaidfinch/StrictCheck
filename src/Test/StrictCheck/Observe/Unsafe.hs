{-| This module defines the underlying __unsafe__ primitives StrictCheck uses
    to implement purely functional observation of evaluation.

    The "functions" in this module are __not referentially transparent__!
-}
module Test.StrictCheck.Observe.Unsafe where

import System.IO.Unsafe
import Data.IORef

import Data.Bifunctor
import Generics.SOP (I(..), unI)

import Test.StrictCheck.Shaped
import Test.StrictCheck.Demand

-- | From some value of any type, produce a pair: a copy of the original value,
-- and a 'Thunk' of that same type, with their values determined by the
-- /order/ in which their values themselves are evaluated
--
-- If the copy of the value is evaluated to weak-head normal form before the
-- returned @Thunk@, then any future inspection of the @Thunk@ will show that it
-- is equal to the original value wrapped in an @Eval@. However, if the copy of
-- the value is /not/ evaluated by the time the @Thunk@ is evaluated, any future
-- inspection of the @Thunk@ will show that it is equal to @Thunk@.
--
-- A picture may be worth 1000 words:
--
-- >>> x = "hello," ++ " world"
-- >>> (x', t) = entangle x
-- >>> x'
-- "hello, world"
-- >>> t
-- Eval "hello, world"
--
-- >>> x = "hello," ++ " world"
-- >>> (x', t) = entangle x
-- >>> t
-- Thunk
-- >>> x'
-- "hello, world"
-- >>> t
-- Thunk
{-# NOINLINE entangle #-}
entangle :: forall a. a -> (a, Thunk a)
entangle a =
  unsafePerformIO $ do
    ref <- newIORef Thunk
    return ( unsafePerformIO $ do
               writeIORef ref (Eval a)
               return a
           , unsafePerformIO $ readIORef ref )

-- | Recursively 'entangle' an @a@, producing not merely a @Thunk@, but an
-- entire @Demand@ which is piecewise entangled with that value. Whatever
-- portion of the entangled value is evaluated before the corresponding portion
-- of the returned @Demand@ will be represented in the shape of that @Demand@.
-- However, any part of the returned @Demand@ which is evaluated before the
-- corresponding portion of the entangled value will be forever equal to
-- @Thunk@.
--
-- The behavior of this function is even more tricky to predict than that of
-- 'entangle', especially when evaluation of the entangled value and the
-- corresponding @Demand@ happen at the same time. In StrictCheck, all
-- evaluation of the entangled value occurs before any evaluation of the
-- @Demand@; we never interleave their evaluation.
{-# NOINLINE instrument #-}
instrument :: Shaped a => a -> (a, Demand a)
instrument =
  first (fuse unI)
  . unzipWith entangle'
  . interleave I
  where
    entangle' :: I x -> (I x, Thunk x)
    entangle' =
      first I . entangle . unI
