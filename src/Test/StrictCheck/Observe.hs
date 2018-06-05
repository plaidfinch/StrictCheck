{-| This module implements the core "trick" of StrictCheck: observing the
    demand behavior of a function in a purely functional way.

    All the functions in this module are safe and referentially transparent.

    Observing the evaluation of a function using these functions incurs at most
    a small constant multiple of overhead compared to just executing the function
    with no observation.
-}
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

-- | Observe the demand behavior
--
-- * in a given evaluation context,
-- * of a given __unary function__,
-- * called upon a given input,
--
-- returning a pair of
--
-- * the demand on its output exerted by the evaluation context, and
-- * the demand on its input this induced
--
-- Suppose we want to see how strict @reverse@ is when we evaluate its result
-- to weak-head normal form:
--
-- >>> (b, a) = observe1 (`seq` ()) (reverse @Int) [1, 2, 3]
-- >>> printDemand b  -- output demand
-- _ : _
-- >>> printDemand a  -- input demand
-- _ : _ : _ : _ : []
--
-- This tells us that our context did indeed evaluate the result of @reverse@
-- to force only its first constructor, and that doing so required the entire
-- spine of the list to be evaluated, but did not evaluate any of its elements.
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

-- | Observe the demand behavior
--
-- * in a given evaluation context
-- * of a given __uncurried n-ary function__ (taking as input an n-ary
-- product of inputs represented as an 'NP' 'I' from "Generics.SOP")
-- * called upon all of its inputs (provided as curried ordinary inputs),
--
-- returning a pair of
--
-- * the demand on its output exerted by the evaluation context, and
-- * the demands on its inputs this induced, represented as an 'NP' 'Demand'
-- from "Generics.SOP"
--
-- This is mostly useful for implementing the internals of StrictCheck;
-- 'observe' is more ergonomic for exploration by end-users.
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

-- | Observe the demand behavior
--
-- * in a given evaluation context
-- * of a given __curried n-ary function__
-- * called upon all of its inputs (provided as curried ordinary inputs),
--
-- returning a pair of
--
-- * the demand on its output exerted by the evaluation context, and
-- * the demands on its inputs this induced, represented as an 'NP' 'Demand'
-- from "Generics.SOP"
--
-- This function is variadic and curried: it takes @n + 2@ arguments, where
-- @n@ is the total number of arguments taken by the observed function.
--
-- Suppose we want to see how strict @zipWith (*)@ is when we evaluate its
-- result completely (to normal form):
--
-- >>> productZip = zipWith ((*) @Int)
-- >>> (zs, (xs :* ys :* Nil)) = observe normalize productZip [10, 20] [30, 40]
-- >>> printDemand zs  -- output demand
-- 300 : 800 : []
-- >>> printDemand xs  -- input demand #1
-- 10 : 20 : []
-- >>> printDemand ys  -- input demand #2
-- 30 : 40 : _
--
-- If you haven't thought very carefully about the strictness behavior of @zip@,
-- this may be a surprising result; this is part of the fun!
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
