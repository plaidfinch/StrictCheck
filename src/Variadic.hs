{-# language TypeFamilyDependencies, GADTs, TypeInType, TypeOperators, TypeApplications, MultiParamTypeClasses, FlexibleInstances, FlexibleContexts, AllowAmbiguousTypes, ScopedTypeVariables, UndecidableInstances #-}

module Variadic where

import Data.Kind
import Data.Functor.Bind

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
data TList (ts :: [k]) where
  TNil  :: TList '[]
  TCons :: TList ts -> TList (t : ts)

-- For *literally* any list of types, we can produce such a proxy
class                     KnownTypes (ts :: [k]) where types :: TList ts
instance                  KnownTypes '[]         where types = TNil
instance KnownTypes ts => KnownTypes (t : ts)    where types = TCons types

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
  WithoutArgs '[]        f           = f
  WithoutArgs (a : args) (a -> rest) = WithoutArgs args rest

-- Strip all arguments from a function type, yielding its (non-function) result
type Result f = WithoutArgs (Args f) f

--------------------------------------------------------------------------------
-- Collapsing curried functions into data structures

-- A "variad" represents some n-ary function, collapsed into a pseudo-list
data Variad (args :: [*]) (res :: *) where
  Res :: res -> Variad '[] res
  Arg :: (a -> Variad args res) -> Variad (a : args) res

runVariad :: Variad (a : args) res -> a -> Variad args res
runVariad (Arg f) = f

-- It's a functor...
instance Functor (Variad args) where
  fmap f (Res res)    = Res (f res)
  fmap f (Arg lambda) = Arg (\a -> fmap f (lambda a))

-- And an applicative
instance Applicative (Variad '[]) where
  pure = Res
  Res f <*> Res a = Res (f a)

instance Applicative (Variad args) => Applicative (Variad (a : args)) where
  pure = Arg . const . pure
  Arg l <*> Arg m = Arg (\a -> l a <*> m a)

-- Variad is also a monad, but the instance would be annoying to write,
-- and we don't think it's very useful. Feel free to prove us wrong :)

-- We can apply a variad to a matching list of arguments
applyVariad :: Variad args res -> HList args -> res
applyVariad (Res res)    HNil         = res
applyVariad (Arg lambda) (a ::: rest) = applyVariad (lambda a) rest

-- Or we can extract the curried function it represents
expandVariad :: Variad args res -> WithArgs args res
expandVariad (Res res)    = res
expandVariad (Arg lambda) = \a -> expandVariad (lambda a)

--------------------------------------------------------------------------------
-- A chutney is kind of like a curry, but stronger

-- The Chutney class lets us embed a function in a variad, or extract it
-- This is yet another "inductive typeclass" definition
class Chutney (args :: [*]) (function :: *) where
   collapse :: function -> Variad args (WithoutArgs args function)
   expand   :: Variad args (WithoutArgs args function) -> function

-- We can always move back and forth between a (Res x) and an x
instance Chutney '[] x where
  collapse x     = Res x
  expand (Res x) = x

-- And if we know how to move back and forth between a variad on args & rest and
-- its corresponding function, we can do the same if we add one more argument
-- to the front of the list and to its corresponding function
instance Chutney args rest => Chutney (a : args) (a -> rest) where
  collapse f     = Arg (\a -> collapse (f a))
  expand (Arg f) = \a -> expand (f a)

-- Collapsing *all* arguments to a function is a special case of the above;
-- indeed, it has the same definition, but with a more specific types
collapseAll :: Chutney (Args function) function
            => function -> Variad (Args function) (Result function)
collapseAll = collapse

-- Likewise, we can fully expand a function from its corresponding variad
expandAll :: Chutney (Args function) function
          => Variad (Args function) (Result function) -> function
expandAll = expand

-- Additionally, we can transform a function from a heterogeneous list to some
-- result into a variad.
collect :: KnownTypes xs => (HList xs -> res) -> Variad xs res
collect k = go types k
  where
    -- This has to use CPS style because of contravariance? I think?
    go :: TList xs -> (HList xs -> res) -> Variad xs res
    go TNil       k = Res (k HNil)
    go (TCons ts) k = Arg (\a -> go ts (k . (a :::)))

--------------------------------------------------------------------------------
-- And now, the punchline: variadic currying/uncurrying, aka (un)chutney-ing

unchutney :: Chutney (Args function) function
          => function
          -> (HList (Args function) -> Result function)
unchutney = applyVariad . collapseAll

chutney :: (Chutney (Args function) function, KnownTypes (Args function))
        => (HList (Args function) -> Result function)
        -> function
chutney f = expandAll (collect f)
