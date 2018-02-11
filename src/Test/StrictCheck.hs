
{-# OPTIONS_GHC -fno-warn-dodgy-exports -fno-warn-unused-imports #-}

module Test.StrictCheck
  -- ( module Test.StrictCheck.Curry
  -- , module Test.StrictCheck.Produce
  -- , module Test.StrictCheck.Consume
  -- , module Test.StrictCheck.Observe
  -- , module Test.StrictCheck.Instances
  -- , module Test.StrictCheck.Demands

  -- , module Generics.SOP
  -- , module Generics.SOP.NP
  -- )
  where


import Test.StrictCheck.Curry
import Test.StrictCheck.Produce
import Test.StrictCheck.Consume
import Test.StrictCheck.Observe
import Test.StrictCheck.Instances
import Test.StrictCheck.Demands
import Test.StrictCheck.Shaped
import Test.StrictCheck.Shaped.Flattened

import Generics.SOP
import Generics.SOP.NP
import qualified GHC.Generics as GHC

import Test.QuickCheck
import Data.List

-- TODO: Think hard about what particular things to export from Generics.SOP
-- and, indeed, our own modules. And which modules to export other modules from

-- TODO: Get rid of these functions once we hit production...

import Test.StrictCheck.Internal.Inputs
import Control.DeepSeq

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

data Binary =
  N Binary Binary | L
  deriving stock (Eq, Ord, Show, GHC.Generic)
  deriving anyclass (Generic, HasDatatypeInfo, Consume, Shaped)

binary :: Int -> Binary
binary 0 = L
binary n = N (binary (n - 1)) (binary (n - 1))

data Omega = Succ Omega -- | Zero
  deriving stock (Eq, Ord, Show, GHC.Generic)
  deriving anyclass (Generic, HasDatatypeInfo, Consume, Shaped, NFData)

data D = C ()
  deriving stock (GHC.Generic, Show)
  deriving anyclass (Generic, HasDatatypeInfo, Consume, Shaped, NFData)

instance Produce Omega where
  produce input = Succ <$> recur input

omega :: Omega
omega = Succ omega

treeToOmega :: IO (Binary -> Omega)
treeToOmega = generate (freely produce)

forceOmegaN :: Int -> Omega -> ()
forceOmegaN 0 _        = ()
forceOmegaN n (Succ o) = forceOmegaN (n - 1) o

forceBinaryN :: Int -> Binary -> ()
forceBinaryN _ L = ()
forceBinaryN 0 _ = ()
forceBinaryN n (N l r) =
  forceBinaryN (pred n) l `seq` forceBinaryN (pred n) r

observeTreeToOmega :: (Binary -> Omega) -> Int -> Int -> Demand Binary
observeTreeToOmega f m n = snd $ observe1 (forceOmegaN n) f (binary m)
