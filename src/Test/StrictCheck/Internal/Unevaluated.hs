module Test.StrictCheck.Internal.Unevaluated where

import Control.Exception

data Unevaluated = Unevaluated deriving Show

instance Exception Unevaluated
