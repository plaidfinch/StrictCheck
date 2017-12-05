
{-# OPTIONS_GHC -fno-warn-dodgy-exports -fno-warn-unused-imports #-}

module Test.StrictCheck
  ( module Test.StrictCheck.Variadic
  , module Test.StrictCheck.Produce
  , module Test.StrictCheck.Consume
  , module Test.StrictCheck.Instances

  , module Test.StrictCheck.Scratch.Observe
  , module Test.StrictCheck.Scratch.LazyCoArbitrary
  , module Test.StrictCheck.Scratch.Nats
  ) where


import Test.StrictCheck.Variadic
import Test.StrictCheck.Produce
import Test.StrictCheck.Consume
import Test.StrictCheck.Instances

import Test.StrictCheck.Scratch.Observe
import Test.StrictCheck.Scratch.LazyCoArbitrary
import Test.StrictCheck.Scratch.Nats
