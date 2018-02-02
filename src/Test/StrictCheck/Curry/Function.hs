module Test.StrictCheck.Curry.Function where

import Generics.SOP

-------------------------------------------------------
-- Collapsing curried functions into data structures --
-------------------------------------------------------

-- A Function represents some n-ary function, uncurried into a pseudo-list
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
applyFunction :: Function args res -> NP I args -> res
applyFunction (Res res)    Nil           = res
applyFunction (Arg lambda) (I a :* rest) = applyFunction (lambda a) rest

-- Additionally, we can transform a function from a heterogeneous list to some
-- result into a Function.
toFunction :: SListI xs => (NP I xs -> res) -> Function xs res
toFunction f = go (hpure (K ())) f
  where
    -- The use of CPS style here prevents quadratic blowup
    go :: NP (K ()) xs -> (NP I xs -> res) -> Function xs res
    go Nil       k = Res (k Nil)
    go (_ :* ts) k = Arg (\a -> go ts (k . (I a :*)))
