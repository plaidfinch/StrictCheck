{-| __Internal module__: This module does not make any stability guarantees, and
    may not adhere to the PVP.

    This module defines the 'Omega' type, which has only one inhabitant: the
    infinite chain of successors. Any function which consumes an @Omega@ is
    functionally equivalent to any other; likewise for those which produce an
    @Omega@. However, they may have radically differing strictness behaviors. It
    is for this reason that we have use for this type in the course of random
    example generation.
-}
module Test.StrictCheck.Internal.Omega
  ( Omega(..)
  , forceOmega
  ) where

import Test.StrictCheck.Produce
import Test.StrictCheck.Shaped

import qualified GHC.Generics as GHC
import Generics.SOP

-- | The type with one inhabitant: the infinite chain of successors
data Omega = Succ Omega
  deriving (GHC.Generic, Generic, HasDatatypeInfo, Shaped)

instance Produce Omega where
  produce = Succ <$> recur

-- | Evaluate @n@ constructors of a given @Omega@ value, returning unit
forceOmega :: Int -> Omega -> ()
forceOmega n o
  | n <= 0
  = ()
  | Succ o' <- o
  = forceOmega (n - 1) o'
