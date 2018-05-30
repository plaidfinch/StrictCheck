module Test.StrictCheck.Observe.Unsafe where

import System.IO.Unsafe
import Data.IORef

import Data.Bifunctor
import Generics.SOP (I(..), unI)

import Test.StrictCheck.Shaped
import Test.StrictCheck.Demand

{-# NOINLINE entangle #-}
entangle :: forall a. a -> (a, Thunk a)
entangle a =
  unsafePerformIO $ do
    ref <- newIORef Thunk
    return ( unsafePerformIO $ do
               writeIORef ref (Eval a)
               return a
           , unsafePerformIO $ readIORef ref )

{-# NOINLINE entangleShape #-}
entangleShape :: Shaped a => a -> (a, Demand a)
entangleShape =
  first (fuse unI)
  . (\(Pair l r) -> (l, r))
  . separate (uncurry Pair . first I . entangle . unI)
  . (I %)
