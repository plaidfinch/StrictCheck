module Test.StrictCheck.Observe
  ( observe1
  , observe
  , observeNP
  ) where

import Data.Bifunctor
import Data.Functor.Product

import Generics.SOP hiding (Shape)

import Test.StrictCheck.Curry hiding (curry, uncurry)
import Test.StrictCheck.Shaped
import Test.StrictCheck.Observe.Unsafe
import Test.StrictCheck.Demand

------------------------------------------------------
-- Observing demand behavior of arbitrary functions --
------------------------------------------------------

observe1
  :: (Shaped a, Shaped b)
  => (b -> ()) -> (a -> b) -> a -> (Demand b, Demand a)
observe1 context function input =
  let (input', inputD)  =
        entangleShape input              -- (1)
      (result', resultD) =
        entangleShape (function input')  -- (2)
  in let !_ = context result'            -- (3)
  in (resultD, inputD)                   -- (4)

observeNP
  :: (All Shaped inputs, Shaped result)
  => (result -> ())
  -> (NP I inputs -> result)
  -> NP I inputs
  -> ( Demand result
     , NP Demand inputs )
observeNP context function inputs =
  let entangled =
        hcliftA
          (Proxy @Shaped)
          (uncurry Pair . first I . entangleShape . unI)
          inputs
      (inputs', inputsD) =
        (hliftA (\(Pair r _) -> r) entangled,
          hliftA (\(Pair _ l) -> l) entangled)
      (result', resultD) = entangleShape (function inputs')
  in let !_ = context result'
  in (resultD, inputsD)

observe
  :: ( All Shaped (Args function)
     , Shaped (Result function)
     , Curry (Args function) )
  => (Result function -> ())
  -> function
  -> Args function
  ⋯-> ( Demand (Result function)
       , NP Demand (Args function) )
observe context function =
  curryAll (observeNP context (uncurryAll function))
