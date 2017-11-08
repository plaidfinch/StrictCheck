{-# language TypeFamilyDependencies, GADTs, TypeInType, TypeOperators, TypeApplications, MultiParamTypeClasses, FlexibleInstances, FlexibleContexts, AllowAmbiguousTypes, ScopedTypeVariables, UndecidableInstances #-}

module Variadic where

import Data.Kind
import Data.Functor.Bind

--------------------------------------------------------------------------------

type family All (f :: k -> Constraint) (ts :: [k]) :: Constraint where
  All f '[]      = ()
  All f (t : ts) = (f t, All f ts)

--------------------------------------------------------------------------------

data HList (ts :: [k]) where
  HNil  :: HList '[]
  (:::) :: t -> HList ts -> HList (t : ts)

instance (All Show ts) => Show (HList ts) where
  show HNil       = "HNil"
  show (x ::: xs) = show x ++ " ::: " ++ show xs

data TList (ts :: [k]) where
  TNil  :: TList '[]
  TCons :: TList ts -> TList (t : ts)

class KnownTypes (ts :: [k]) where
  types :: TList ts

instance KnownTypes '[] where
  types = TNil

instance KnownTypes ts => KnownTypes (t : ts) where
  types = TCons types

--------------------------------------------------------------------------------

type family Args (f :: *) :: [*] where
  Args (a -> rest) = a :  Args rest
  Args x           = '[]

type Result f = WithoutArgs (Args f) f

type family WithoutArgs (args :: [*]) (f :: *) :: * where
  WithoutArgs '[]        f           = f
  WithoutArgs (a : args) (a -> rest) = WithoutArgs args rest

type family WithArgs (args :: [*]) (rest :: *) :: * where
  WithArgs '[]        rest = rest
  WithArgs (a : args) rest = a -> WithArgs args rest

--------------------------------------------------------------------------------

data Variad (args :: [*]) (res :: *) where
  Res :: res -> Variad '[] res
  Arg :: (a -> Variad args res) -> Variad (a : args) res

instance Functor (Variad args) where
  fmap f (Res res)    = Res (f res)
  fmap f (Arg lambda) = Arg (\a -> fmap f (lambda a))

instance Apply (Variad args) where
  Res f <.> Res a = Res (f a)
  Arg l <.> Arg m = Arg (\a -> (l a) <.> (m a))

applyVariad :: Variad args res -> HList args -> res
applyVariad (Res res)    HNil         = res
applyVariad (Arg lambda) (a ::: rest) = applyVariad (lambda a) rest

expandVariad :: Variad args res -> WithArgs args res
expandVariad (Res res)    = res
expandVariad (Arg lambda) = \a -> expandVariad (lambda a)

--------------------------------------------------------------------------------

class Chutney (args :: [*]) (function :: *) where
   collapse :: function -> Variad args (WithoutArgs args function)
   expand   :: Variad args (WithoutArgs args function) -> function

instance Chutney '[] x where
  collapse x   = Res x
  expand (Res x) = x

instance Chutney args rest => Chutney (a : args) (a -> rest) where
  collapse f     = Arg (\a -> collapse (f a))
  expand (Arg f) = \a -> expand (f a)

collapseAll :: Chutney (Args function) function
            => function -> Variad (Args function) (Result function)
collapseAll = collapse

expandAll :: Chutney (Args function) function
          => Variad (Args function) (Result function) -> function
expandAll = expand

--------------------------------------------------------------------------------

collect :: KnownTypes xs => (HList xs -> res) -> Variad xs res
collect k = go types k
  where
    go :: TList xs -> (HList xs -> res) -> Variad xs res
    go TNil       k = Res (k HNil)
    go (TCons ts) k = Arg (\a -> go ts (k . (a :::)))

unchutney :: Chutney (Args function) function
          => function
          -> (HList (Args function) -> Result function)
unchutney = applyVariad . collapseAll

chutney :: (Chutney (Args function) function, KnownTypes (Args function))
        => (HList (Args function) -> Result function)
        -> function
chutney f = expandAll (collect f)
