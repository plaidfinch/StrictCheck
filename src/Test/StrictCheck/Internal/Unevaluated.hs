{-| This module defines the internal exception type used to implement the
    to/from-Demand methods in "Test.StrictCheck.Demand". We don't export this
    type from the library to discourage users from interacting with this
    mechanism.
-}

module Test.StrictCheck.Internal.Unevaluated
  ( Unevaluated(..)
  ) where

import Control.Exception

-- | In @fromDemand@, this exception is (purely, lazily) thrown whenever a
-- @Thunk@ is encountered. In @toDemand@, it is caught and converted back to a
-- @Thunk@.
data Unevaluated
  = Unevaluated
  deriving Show

instance Exception Unevaluated
