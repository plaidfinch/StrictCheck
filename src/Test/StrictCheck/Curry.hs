{-| This module defines a flexible and efficient way to curry and uncurry
    functions of any arity. This is useful in the context of StrictCheck to
    provide a lightweight interface to test developers which does not require
    them to directly work with heterogeneous lists.
-}
module Test.StrictCheck.Curry
  ( -- * Computing the types of curried functions
    type (⋯->)
  , type (-..->)
  , Args
  , Result
  -- * Currying functions at all arities
  , Curry(..)
  , curryAll
  , uncurryAll
  , withCurryIdentity
  -- * Generalized to any heterogeneous list
  , List(..)
  ) where


import Prelude hiding (curry, uncurry)

import Data.Kind (Type)
import Data.Type.Equality
import qualified Unsafe.Coerce as UNSAFE

import qualified Generics.SOP as SOP


-------------------------------------------------
-- Manipulating the types of curried functions --
-------------------------------------------------

-- | Given a function type, return a list of all its argument types
--
-- For example:
--
-- > Args (Int -> Bool -> Char)  ~  [Int, Bool]
type family Args (f :: Type) :: [Type] where
  Args (a -> rest) = a : Args rest
  Args x           = '[]

-- | Given a list of argument types and the "rest" of a function type, return a
-- curried function type which takes the specified argument types in order,
-- before returning the given rest
--
-- For example:
--
-- > [Int, Bool] ⋯-> Char  ~  Int -> Bool -> Char
--
-- This infix unicode symbol is meant to evoke a function arrow with an
-- ellipsis.
type family (args :: [Type]) ⋯-> (rest :: Type) :: Type where
  '[]        ⋯-> rest = rest
  (a : args) ⋯-> rest = a -> args ⋯-> rest

-- | For those who don't want to type in unicode, we provide this ASCII synonym
-- for the ellipsis function arrow @(⋯->)@
type args -..-> rest = args ⋯-> rest

-- | Strip all arguments from a function type, yielding its (non-function-type)
-- result
--
-- For example:
--
-- > Result (Int -> Bool -> Char)  ~  Char
type family Result (f :: Type) :: Type where
  Result (a -> rest) = Result rest
  Result r           = r

curryIdentity :: forall function.
  function :~: (Args function ⋯-> Result function)
curryIdentity = UNSAFE.unsafeCoerce (Refl :: () :~: ())

-- | For any function type @function@, it is always true that
--
-- > function  ~  (Args function ⋯-> Result function)
--
-- GHC doesn't know this, however, so @withCurryIdentity@ provides this proof to
-- the enclosed computation, by discharging this wanted equality constraint.
withCurryIdentity :: forall function r.
  (function ~ (Args function ⋯-> Result function) => r) -> r
withCurryIdentity r =
  case curryIdentity @function of Refl -> r


------------------------
-- Partial uncurrying --
------------------------

-- | This currying mechanism is agnostic to the concrete heterogeneous list type
-- used to carry arguments. The @List@ class abstracts over the nil and cons
-- operations of a heterogeneous list: to use your own, just define an instance.
class List (list :: [Type] -> Type) where
  nil    :: list '[]
  cons   :: x -> list xs -> list (x : xs)
  uncons :: list (x : xs) -> (x, list xs)

-- | The Curry class witnesses that for any list of arguments, it is always
-- possible to curry/uncurry at that arity
class Curry (args :: [Type]) where
  uncurry
    :: forall result list.
    List list => (args ⋯-> result) -> list args -> result
  curry
    :: forall result list.
    List list => (list args -> result) -> args ⋯-> result

instance Curry '[] where
  uncurry x = \(!_) -> x
  curry   f = f nil

instance Curry xs => Curry (x : xs) where
  uncurry f = \(uncons -> (x, xs)) -> uncurry (f x) xs
  curry   f = \x -> curry (\xs -> f (cons x xs))


--------------------------------------------------------
-- Variadic uncurrying/currying, aka (un)curryAll-ing --
--------------------------------------------------------

-- | Uncurry all arguments to a function type
--
-- This is a special case of 'uncurry', and may ease type inference.
uncurryAll
  :: forall function list. (List list, Curry (Args function))
  => function -> (list (Args function) -> Result function)
uncurryAll = withCurryIdentity @function uncurry

-- | Curry all arguments to a function from a heterogeneous list to a result
--
-- This is a special case of 'curry', and may ease type inference.
curryAll
  :: forall args result list. (List list, Curry args)
  => (list args -> result)
  -> (args ⋯-> result)
curryAll = curry


--------------------------
-- Instances for HLists --
--------------------------

instance List (SOP.NP SOP.I) where
  nil = SOP.Nil
  cons x xs = SOP.I x SOP.:* xs
  uncons (SOP.I x SOP.:* xs) = (x, xs)
