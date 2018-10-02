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
  , entangle
  , entangleShape
  ) where

import Data.Bifunctor
import Data.Functor.Product
import Data.Functor.Compose
import Data.IORef
import System.IO.Unsafe

import Generics.SOP hiding (Shape)

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
observe1 context function input = unsafePerformIO $ do
  (input',  inputD)  <- entangleShape input             -- (1)
  (result', resultD) <- entangleShape (function input') -- (2)
  let !_ = context result'                              -- (3)
  (,) <$> resultD <*> inputD                            -- (4)

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
observeNP context function inputs = unsafePerformIO $ do
  entangled <-
    hctraverse'
      (Proxy @Shaped)
      (fmap (uncurry Pair . bimap I Compose) . entangleShape . unI)
      inputs
  let (inputs', inputsD) =
        (hliftA     (\(Pair r _) -> r           ) entangled,
         htraverse' (\(Pair _ l) -> getCompose l) entangled)
  (result', resultD) <- entangleShape (function inputs')
  let !_ = context result'
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

-- | 'entangle' allows us to observe whether a value has been forced or not.
-- The resulting 'IO' action creates a tuple with a value equal to the original
-- value and another 'IO' action that when run gives us information whether the
-- returned has been value forced.
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
  return (unsafePerformIO $ do
             writeIORef ref (Eval a)
             return a,
          readIORef ref)

-- | Recursively entangles a value providing us with information about what
-- parts of the value have already been evaluated. See 'entangle'.
--
-- >>> (x, d) <- second (fmap prettyDemand) <$> entangleShape [1..]
-- >>> d
-- "_"
-- >>> length . take 3 $ x
-- 3
-- >>> d
-- "_ : _ : _ : _"
-- >>> take 2 x
-- [1,2]
-- >>> d
-- "1 : 2 : _ : _"
entangleShape :: Shaped a => a -> IO (a, IO (Demand a))
entangleShape = entangleShape' . project I
  -- NOTE: There are a two properties we care about:
  --
  --   1. Running the Demand action should always result in a consistent state
  --      and not depend on when its result is forced.
  --   2. We want to evaluate the input as little as possible. Importantly
  --      running the demand action should never force any previously unforced
  --      parts of the input. This is especially important for the observe
  --      functions and the hardest thing to get right.
  where
    entangleShape' :: forall a. Shaped a => Shape a I -> IO (a, IO (Demand a))
    entangleShape' s =
      (fmap (bimap fst (fmap Wrap . traverse snd =<<)) . entangle =<<)
      . unsafeInterleaveIO $
        match @a s s (\flatA _ ->
          fmap (\flat' ->
            let a = embed unI
                  . unflatten
                  . mapFlattened @Shaped (I . demanded)
                  $ flat'
                ds = fmap unflatten
                   . traverseFlattened @Shaped getDemand
                   $ flat'
            in (a, ds))
          . traverseFlattened @Shaped
            ((uncurry WithDemand <$>) . entangleShape . unI)
          $ flatA)

-- Auxiliary functor for the traversal in 'entangleShape'
data WithDemand a
  = WithDemand { demanded :: a, getDemand :: IO (Demand a) }
