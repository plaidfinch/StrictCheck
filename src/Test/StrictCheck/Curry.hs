{-# LANGUAGE PatternSynonyms #-}

module Test.StrictCheck.Curry
  ( Args
  , Result
  , type (-..->)
  , type (⋯->)
  , Curry(..)
  , Cons1(..)
  , Cons(..)
  , Nil(..)
  -- , pattern (:&:)
  -- , pattern (:&)
  -- , pattern Nil
  , withCurryIdentity
  , curryAll
  , uncurryAll
  ) where


import Prelude hiding (curry, uncurry)

import Data.Type.Equality
import qualified Unsafe.Coerce as UNSAFE

import qualified Generics.SOP as SOP


-------------------------------------------------
-- Manipulating the types of curried functions --
-------------------------------------------------

-- Given a function, return a list of all its argument types
type family Args (f :: *) :: [*] where
  Args (a -> rest) = a : Args rest
  Args x           = '[]

-- Given a list of argument types and a "rest" of type return a curried function
type family (args :: [*]) ⋯-> (rest :: *) :: * where
  '[]        ⋯-> rest = rest
  (a : args) ⋯-> rest = a -> args ⋯-> rest

type args -..-> rest = args ⋯-> rest

-- Strip all arguments from a function type, yielding its (non-function) result
type family Result (f :: *) :: * where
  Result (a -> rest) = Result rest
  Result r           = r

curryIdentity :: forall function.
  function :~: (Args function ⋯-> Result function)
curryIdentity = UNSAFE.unsafeCoerce (Refl :: () :~: ())

withCurryIdentity :: forall function r.
  (function ~ (Args function ⋯-> Result function) => r) -> r
withCurryIdentity r = case curryIdentity @function of Refl -> r


------------------------
-- Partial uncurrying --
------------------------

class Nil (list :: [*] -> *) where
  nil :: list '[]

class Nil list => Cons (list :: [*] -> *) where
  cons   :: x -> list xs -> list (x : xs)
  uncons :: list (x : xs) -> (x, list xs)

class Cons1 (list :: (k -> *) -> [k] -> *) where
  cons1   :: f x -> list f xs -> list f (x : xs)
  uncons1 :: list f (x : xs) -> (f x, list f xs)

-- pattern Nil :: Nil list => list '[]
-- pattern Nil <- !_ where Nil = nil

-- pattern (:&) :: Cons list => x -> list xs -> list (x : xs)
-- pattern x :& xs <- (uncons -> (x, xs)) where x :& xs = cons x xs

-- pattern (:&:) :: Cons1 list => f x -> list f xs -> list f (x : xs)
-- pattern x :&: xs <- (uncons1 -> (x, xs)) where x :&: xs = cons1 x xs

class Curry (args :: [*]) where
  uncurry :: Cons list => (args ⋯-> result) -> list args -> result
  curry   :: Cons list => (list args -> result) -> args ⋯-> result

instance Curry '[] where
  uncurry x = \(!_) -> x
  curry   f = f nil

instance Curry xs => Curry (x : xs) where
  uncurry f = \(uncons -> (x, xs)) -> uncurry (f x) xs
  curry   f = \x -> curry (f . (cons x))


--------------------------------------------------------
-- Variadic uncurrying/currying, aka (un)curryAll-ing --
--------------------------------------------------------

uncurryAll
  :: forall function list. (Cons list, Curry (Args function))
  => function -> (list (Args function) -> Result function)
uncurryAll = withCurryIdentity @function uncurry

curryAll
  :: forall args result list. (Cons list, Curry args)
  => (list args -> result)
  -> (args ⋯-> result)
curryAll = curry


--------------------------
-- Instances for HLists --
--------------------------

instance Nil (SOP.NP f) where
  nil = SOP.Nil

instance Cons (SOP.NP SOP.I) where
  cons x xs = SOP.I x SOP.:* xs
  uncons (SOP.I x SOP.:* xs) = (x, xs)

instance Cons1 SOP.NP where
  cons1 x xs = x SOP.:* xs
  uncons1 (x SOP.:* xs) = (x, xs)
