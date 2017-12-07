{-# language DataKinds, GADTs, KindSignatures, BangPatterns, TypeFamilies,
  RankNTypes, AllowAmbiguousTypes, UndecidableInstances, PolyKinds,
  DefaultSignatures, TypeOperators, EmptyCase, LambdaCase,
  TypeApplications, ScopedTypeVariables, FlexibleContexts, ConstraintKinds #-}

module Test.StrictCheck.Observe where

import Data.IORef
import System.IO.Unsafe

import Data.Kind ( Type )
import GHC.Generics
import Data.Void

data DemandKind = Observing | Describing

data Thunk a = E !a | T

data Field (a :: Type) (t :: DemandKind) where
  F ::        Thunk (Demand a 'Describing) -> Field a 'Describing
  R :: IORef (Thunk (Demand a 'Observing)) -> Field a 'Observing

class Observe (a :: Type) where
  type Demand a :: DemandKind -> Type

  observe :: (forall x. Observe x => x -> (x, Field x t))
          -> a -> (a, Demand a t)

  reify :: (forall x. Field x s -> Field x t)
        -> Demand a s -> Demand a t

  force :: (forall x. Observe x => Field x t -> x -> ())
        -> Demand a t -> a -> ()
