module Test.StrictCheck.Curry
  ( Args
  , Result
  , type (-..->)
  , Curry(..)
  , uncurryAll
  , curryAll
  , withCurryIdentity
  ) where

import Generics.SOP
import Test.StrictCheck.Curry.Function

import Data.Type.Equality
import qualified Unsafe.Coerce as UNSAFE


-------------------------------------------------
-- Manipulating the types of curried functions --
-------------------------------------------------

-- Given a function, return a list of all its argument types
type family Args (f :: *) :: [*] where
  Args (a -> rest) = a : Args rest
  Args x           = '[]

-- Given a list of argument types and a "rest" of type return a curried function
type family (args :: [*]) -..-> (rest :: *) :: * where
  '[]        -..-> rest = rest
  (a : args) -..-> rest = a -> args -..-> rest

-- Strip all arguments from a function type, yielding its (non-function) result
type family Result (f :: *) :: * where
  Result (a -> rest) = Result rest
  Result r           = r

curryIdentity :: forall function.
  function :~: (Args function -..-> Result function)
curryIdentity = UNSAFE.unsafeCoerce (Refl :: () :~: ())

withCurryIdentity :: forall function r.
  (function ~ (Args function -..-> Result function) => r) -> r
withCurryIdentity r = case curryIdentity @function of Refl -> r

----------------------------------------
-- Partial uncurrying, Functionically --
----------------------------------------

-- | The Curry class lets us embed a function in a Function, or extract it
-- This is yet another "inductive typeclass" definition
class Curry (args :: [*]) (result :: *) where
   uncurryFunction :: (args -..-> result) -> Function args result
   curryFunction   :: Function args result -> (args -..-> result)

-- | We can always move back and forth between a (Res x) and an x
instance Curry '[] x where
  uncurryFunction    x  = Res x
  curryFunction (Res x) =     x

-- | If we know how to move back and forth between a Function on args & result
-- and its corresponding function, we can do the same if we add one more
-- argument to the front of the list and to its corresponding function
instance Curry args result => Curry (a : args) result where
  uncurryFunction    f  = Arg $ \a -> uncurryFunction (f a)
  curryFunction (Arg f) =       \a -> curryFunction   (f a)


--------------------------------------------------------
-- Variadic uncurrying/currying, aka (un)curryAll-ing --
--------------------------------------------------------

uncurryAll :: forall function.
           Curry (Args function) (Result function)
           => function
           -> (NP I (Args function) -> Result function)
uncurryAll =
  withCurryIdentity @function $ applyFunction . uncurryFunction

curryAll :: forall args result.
         (Curry args result, SListI args)
         => (NP I args -> result)
         -> (args -..-> result)
curryAll = curryFunction . toFunction
