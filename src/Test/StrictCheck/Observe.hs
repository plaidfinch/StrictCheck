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
  , instrument
  , entangle
  ) where

import Data.Bifunctor
import Data.Functor.Product
import Data.Functor.Compose
import Data.IORef
import System.IO.Unsafe

import Generics.SOP hiding (Shape, Compose)

import Test.StrictCheck.Curry hiding (curry, uncurry)
import Test.StrictCheck.Shaped
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
  -- Using unsafePerformIO here and in observeNP is safe, as the result of the
  -- IO action only depends on it's inputs and has no side-effects.
  unsafePerformIO $ do

    -- The numbered lines correspond to the NOTE below
    (input',  inputD)  <- instrument input                -- (1)
    (result', resultD) <- instrument (function input')    -- (2)
    let !_ = context result'                              -- (3)
    (,) <$> resultD <*> inputD                            -- (4)

    -- NOTE: The observation function:
    -- (1) instruments the input
    -- (2) instruments the result of the function applied to the input
    -- (3) evaluates the instrumented result of the function in the context, and
    -- (4) returns the observed demands on the result and the input.


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
  -- NOTE: See the comment in observe1 about the safety of unsafePerformIO here.
  unsafePerformIO $ do
    -- This function works identically to observe1, except it has more
    -- line-noise to shuffle around newtypes and traverse heterogeneous lists.
    -- To see this, compare the numbered comments below to their corresponding
    -- line labels in observe1.

    -- (1) instrument the inputs
    entangled <-
      hctraverse'
        (Proxy @Shaped)
        (fmap (uncurry Pair . bimap I Compose) . instrument . unI)
        inputs
    let inputs' = hliftA     (\(Pair r _) -> r           ) entangled
    let inputsD = htraverse' (\(Pair _ l) -> getCompose l) entangled

    -- (2) instrument the result of the function on the instrumented inputs
    (result', resultD) <- instrument (function inputs')

    -- (3) evaluate the instrumented result of the function in the context
    let !_ = context result'

    -- (4) return the resultant observed demands
    (,) <$> resultD <*> inputsD


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


--------------------------------------------------------
-- Instrumenting values to determine their evaluation --
--------------------------------------------------------

-- | Creates a tuple of an instrumented thunk, and an @IO@ action whose return
-- value indicates whether that thunk has yet been evaluated.
--
-- >>> (x, d) <- entangle ()
-- >>> d
-- Thunk
-- >>> x
-- ()
-- >>> d
-- Eval ()

entangle :: a -> IO (a, IO (Thunk a))
entangle a = do
  ref <- newIORef Thunk
  -- Using unsafePerformIO here is safe, i.e. it is referentially transparent,
  -- because the only handle to the mutated IORef is closed over by the IO
  -- action returned as the second element of the resultant tuple, which means
  -- the effect of the unsafePerformIO can only be observed from within IO.
  return (unsafePerformIO $ do
             writeIORef ref (Eval a)
             return a,
          readIORef ref)

-- | Recursively instruments a value, returning a tuple of an instrumented
-- value, and an @IO@ action returning a 'Demand' that corresponds to the
-- portion of the instrumented value which has already been evaluated at the
-- time the action was run.
--
-- >>> (x, d) <- instrument [1..]
-- >>> printDemand =<< d
-- _
-- >>> length . take 3 $ x
-- 3
-- >>> printDemand =<< d
-- _ : _ : _ : _
-- >>> take 2 x
-- [1,2]
-- >>> printDemand =<< d
-- 1 : 2 : _ : _

-- NOTE: There are a two properties we care about:
--
--   1. Running the Demand action should always result in a consistent state
--      and not depend on when its result is forced.
--   2. We want to evaluate the input as little as possible. Importantly
--      running the demand action should never force any previously unforced
--      parts of the input. This is especially important for the observe
--      functions and the hardest thing to get right.

instrument :: forall a. Shaped a => a -> IO (a, IO (Demand a))
instrument a = do
   -- We need to use unsafeInterleaveIO here so that we do not force the value
   -- by matching on it when we bind the result above to entangle it.
   --
   -- Using unsafeInterleaveIO here is safe, as the result of the IO action does
   -- not depend on when it is performed and it doesn't matter if it is never
   -- performed, if it's value is not forced.
   (~(~(a', _), da)) <- entangle =<< unsafeInterleaveIO entangledFields
   return (a', Wrap <$> (traverse snd =<< da))
  where
    -- The to-be-entangled value with all its recursive children entangled
    -- We still need to entangle the value itself
    entangledFields :: IO (a, IO (Shape a Demand))
    entangledFields = do
      entangled <- translateA (pairWithDemand . unI) (project I a)
      let a' = embed unI (translate (I . demanded) entangled)
      return (a', translateA getDemand entangled)

    pairWithDemand :: forall x. Shaped x => x -> IO (WithDemand x)
    pairWithDemand = fmap (uncurry WithDemand) . instrument

-- Auxiliary functor for the traversal in 'instrument'
data WithDemand a
  = WithDemand { demanded :: a, getDemand :: IO (Demand a) }
