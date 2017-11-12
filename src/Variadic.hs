{-# language TypeFamilyDependencies, GADTs, TypeInType, TypeOperators, TypeApplications, MultiParamTypeClasses, FlexibleInstances, FlexibleContexts, AllowAmbiguousTypes, ScopedTypeVariables, UndecidableInstances #-}

module Variadic where

import Data.Kind

--------------------------------------------------------------------------------
-- Assert that all types in a list obey a unary constraint

type family All (f :: k -> Constraint) (ts :: [k]) :: Constraint where
  All f '[]      = ()
  All f (t : ts) = (f t, All f ts)

--------------------------------------------------------------------------------
-- Heterogeneous lists indexed by the types of their contents

data HList (ts :: [*]) where
  HNil  :: HList '[]
  (:::) :: t -> HList ts -> HList (t : ts)

instance (All Show ts) => Show (HList ts) where
  show HNil       = "HNil"
  show (x ::: xs) = show x ++ " ::: " ++ show xs

-- A list of types: this is just a "structural proxy"
data Types (ts :: [k]) where
  NoTypes :: Types '[]
  Types   :: Types ts -> Types (t : ts)

-- For *literally* any list of types, we can produce such a proxy
class                     KnownTypes (ts :: [k]) where types :: Types ts
instance                  KnownTypes '[]         where types = NoTypes
instance KnownTypes ts => KnownTypes (t : ts)    where types = Types types

--------------------------------------------------------------------------------
-- Manipulating the types of curried functions

-- Given a function, return a list of all its argument types
type family Args (f :: *) :: [*] where
  Args (a -> rest) = a : Args rest
  Args x           = '[]

-- Given a list of argument types and a "rest" of type return a curried function
type family WithArgs (args :: [*]) (rest :: *) :: * where
  WithArgs '[]        rest = rest
  WithArgs (a : args) rest = a -> WithArgs args rest

-- Given a list of argument types matching some prefix of the arguments of a
-- curried function type, remove those arguments from the function type
type family WithoutArgs (args :: [*]) (f :: *) :: * where
  WithoutArgs '[]        rest        = rest
  WithoutArgs (a : args) (a -> rest) = WithoutArgs args rest

-- Strip all arguments from a function type, yielding its (non-function) result
type Result f = WithoutArgs (Args f) f

--------------------------------------------------------------------------------
-- Collapsing curried functions into data structures

-- A Function represents some n-ary function, currySomed into a pseudo-list
data Function (args :: [*]) (res :: *) where
  Res :: res -> Function '[] res
  Arg :: (a -> Function args res) -> Function (a : args) res

instance Functor (Function args) where
  fmap f (Res res)    = Res (f res)
  fmap f (Arg lambda) = Arg (\a -> fmap f (lambda a))

instance Applicative (Function '[]) where
  pure = Res
  Res f <*> Res a = Res (f a)

instance Applicative (Function args) => Applicative (Function (a : args)) where
  pure = Arg . const . pure
  Arg l <*> Arg m = Arg (\a -> l a <*> m a)

-- It's also a monad but the instance is really complicated to write & honestly
-- I don't think it's very useful. Left as an exercise to the reader.

-- We can apply a Function to a matching list of arguments
applyFunction :: Function args res -> HList args -> res
applyFunction (Res res)    HNil         = res
applyFunction (Arg lambda) (a ::: rest) = applyFunction (lambda a) rest

-- A nice infix notation for applying a Function
($$) = applyFunction

-- Additionally, we can transform a function from a heterogeneous list to some
-- result into a Function.
toFunction :: KnownTypes xs => (HList xs -> res) -> Function xs res
toFunction k = go types k
  where
    -- The use of CPS style here prevents quadratic blowup
    go :: Types xs -> (HList xs -> res) -> Function xs res
    go NoTypes    k = Res (k HNil)
    go (Types ts) k = Arg (\a -> go ts (k . (a :::)))

--------------------------------------------------------------------------------
-- Partial currying, Functionically

-- The Curry class lets us embed a function in a Function, or extract it
-- This is yet another "inductive typeclass" definition
class Curry (args :: [*]) (function :: *) where
   curryFunction   :: function -> Function args (WithoutArgs args function)
   uncurryFunction :: Function args (WithoutArgs args function) -> function

-- We can always move back and forth between a (Res x) and an x
instance Curry '[] x where
  curryFunction        x  = Res x
  uncurryFunction (Res x) =     x

-- And if we know how to move back and forth between a Function on args & rest and
-- its corresponding function, we can do the same if we add one more argument
-- to the front of the list and to its corresponding function
instance Curry args rest => Curry (a : args) (a -> rest) where
  curryFunction        f  = Arg $ \a -> curryFunction   (f a)
  uncurryFunction (Arg f) =       \a -> uncurryFunction (f a)

--------------------------------------------------------------------------------
-- And now, the punchline: variadic currying/uncurrying, aka (un)curryAll-ing

curryAll :: Curry (Args function) function
         => function
         -> (HList (Args function) -> Result function)
curryAll = applyFunction . curryFunction

uncurryAll :: (Curry (Args function) function, KnownTypes (Args function))
           => (HList (Args function) -> Result function)
           -> function
uncurryAll = uncurryFunction . toFunction
