
{-# OPTIONS_GHC -fno-warn-dodgy-exports -fno-warn-unused-imports #-}

module Test.StrictCheck
  ( module Test.StrictCheck.Curry
  , module Test.StrictCheck.Produce
  , module Test.StrictCheck.Consume
  , module Test.StrictCheck.Observe
  , module Test.StrictCheck.Instances
  , module Test.StrictCheck.Demands

  , module Generics.SOP
  , module Generics.SOP.NP
  ) where


import Test.StrictCheck.Curry
import Test.StrictCheck.Produce
import Test.StrictCheck.Consume
import Test.StrictCheck.Observe
import Test.StrictCheck.Instances
import Test.StrictCheck.Demands

import Generics.SOP
import Generics.SOP.NP

-- TODO: Think hard about what particular things to export from Generics.SOP
