{-# language TypeFamilyDependencies, GADTs, TypeInType, TypeOperators, TypeApplications, MultiParamTypeClasses, FlexibleInstances, AllowAmbiguousTypes, ScopedTypeVariables, UndecidableInstances #-}

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

class Collect (args :: [*]) (function :: *) where
   collect :: function -> Variad args (WithoutArgs args function)

instance Collect '[] x where
  collect x = Res x

instance Collect args rest => Collect (a : args) (a -> rest) where
  collect f = Arg (\a -> collect (f a))

collectAll :: Collect (Args function) function => function -> Variad (Args function) (Result function)
collectAll = collect

--------------------------------------------------------------------------------

unchutney :: Collect (Args function) function => function -> HList (Args function) -> Result function
unchutney f = applyVariad (collectAll f)
