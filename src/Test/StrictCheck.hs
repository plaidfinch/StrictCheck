
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

import Test.QuickCheck
import Data.List

-- TODO: Think hard about what particular things to export from Generics.SOP
-- and, indeed, our own modules.

-- TODO: Get rid of these functions once we hit production...

grid :: Integer -> Integer -> [[(Integer, Integer)]]
grid x y = map (\f -> map f [0..y]) $ map (,) [0..x]

withGrid :: Integer -> Integer -> IO (Integer -> Integer -> Integer)
withGrid x y = do
  f <- generate (freely produce)
  let results = map (map (uncurry f)) (grid x y)
  putStrLn ""
  mapM_ print results
  putStrLn ""
  mapM_ print (transpose results)
  return f
