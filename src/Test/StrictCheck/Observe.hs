{-# language DataKinds, GADTs, KindSignatures, BangPatterns, TypeFamilies,
  RankNTypes, AllowAmbiguousTypes, UndecidableInstances,
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

-- data GField (a :: Type -> Type) (t :: DemandKind) (p :: Type)where
--   GF ::        Thunk (GDemand a 'Describing) -> GField a 'Describing
--   GR :: IORef (Thunk (GDemand a 'Observing)) -> GField a 'Observing

-- toGField :: Demand a ~ GDemand (Rep a) => Field a t -> GField (Rep a) t
-- toGField (F t) = GF t
-- toGField (R t) = GR t

-- fromGField :: Demand a ~ GDemand (Rep a) => GField (Rep a) t -> Field a t
-- fromGField (GF t) = F t
-- fromGField (GR t) = R t

-- type GenericObserve a =
--   (Generic a, GObserve (Rep a), Demand a ~ GDemand (Rep a))

class Observe (a :: Type) where
  type Demand a :: DemandKind -> Type
  -- type Demand a = GDemand (Rep a)

  observe :: (forall x. Observe x => x -> (x, Field x t))
          -> a -> (a, Demand a t)
  -- default observe :: GenericObserve a
  --                 => (forall x. Observe x => x -> (x, Field x t))
  --                 -> a -> (a, Demand a t)
  -- observe observeF a =
  --   let (repA', d) =
  --         gObserve @(Rep a) observeF (from a)
  --   in (to repA', d)

  reify :: (forall x. Field x s -> Field x t)
        -> Demand a s -> Demand a t
  -- default reify :: GenericObserve a
  --               => (forall x. Field x s -> Field x t)
  --               -> Demand a s -> Demand a t
  -- reify reifyF d = gReify @(Rep a) reifyF d

  force :: (forall x. Observe x => Field x t -> x -> ())
        -> Demand a t -> a -> ()
  -- default force :: GenericObserve a
  --               => (forall x. Observe x => Field x t -> x -> ())
  --               -> Demand a t -> a -> ()
  -- force forceF d a = gForce forceF d (from a)

-- class GObserve (a :: Type -> Type) where
--   type GDemand a :: DemandKind -> Type
--   gObserve :: (forall x. Observe x => x -> (x, Field x t))
--            -> a p -> (a p, GDemand a t)
--   gReify   :: (forall x. Field x s -> Field x t)
--            -> GDemand a s -> GDemand a t
--   gForce   :: (forall x. Observe x => Field x t -> x -> ())
--            -> GDemand a t -> a p -> ()

-- instance GObserve U1 where
--   type GDemand U1 = GField U1
--   gObserve _ a =
--     unsafePerformIO $ do
--       ref <- newIORef T
--       return ( unsafePerformIO $ do
--                 writeIORef ref (E One)
--                 return a
--               , One )
--   gReify _ U1 = U1
--   gForce _ U1 U1 = ()

-- instance GObserve V1 where
--   type GDemand V1 = GField V1
--   gReify _ = \case
--   gForce _ _ _ = ()

-- instance GObserve f => GObserve (M1 i t f) where
--   type GDemand (M1 i t f) = GDemand f
--   gReify reifyF gDemand = gReify @f reifyF gDemand
--   gForce forceF gDemand (M1 a) =
--     gForce forceF gDemand a

-- newtype GFields a b t p =
--   GFields (GField a t p :*: GField b t p)

-- instance ( GObserve a, GObserve b) => GObserve (a :*: b) where
--   type GDemand (a :*: b) = GField a  :*: GField b
--   gReify reifyF (dl :*: dr) =
--     Prod (toGField (reifyF (fromGField dl)))
--          (toGField (reifyF (fromGField dr)))
--   gForce forceF (dl :*: dr) (a :*: b) =
--     case ( forceF dl _
--          , undefined ) of
--       ((), ()) -> ()

-- instance ( GObserve a, GObserve b) => GObserve (a :+: b) where
--   type GDemand (a :+: b) = a :+: b
--   gReify reifyF (L1 dl) =
--     L1 (gReify @a reifyF dl)
--   gReify reifyF (R1 dr) =
--     R1 (gReify @b reifyF dr)
--   gForce forceF (L1 dl) (L1 a) = gForce @a forceF dl a
--   gForce forceF (R1 dr) (R1 b) = gForce @b forceF dr b
--   gForce _ (L1 _) (R1 _) = ()
--   gForce _ (R1 _) (L1 _) = ()

-- instance Observe c => GObserve (K1 i c) where
--   type GDemand (K1 i c) = Field c
--   gReify reifyF d = reifyF d
--   gForce forceF d (K1 a) = forceF @c d a
