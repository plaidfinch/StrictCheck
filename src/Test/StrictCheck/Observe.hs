{-# language DataKinds, GADTs, BangPatterns, TypeFamilies, RankNTypes,
  AllowAmbiguousTypes, UndecidableInstances, DefaultSignatures,
  TypeApplications, ScopedTypeVariables, FlexibleContexts, ConstraintKinds,
  DeriveFunctor, FlexibleInstances, StandaloneDeriving, DeriveGeneric,
  DeriveAnyClass, TypeOperators, PolyKinds #-}

{-# OPTIONS_GHC -fno-warn-unused-imports #-}

module Test.StrictCheck.Observe where

import Data.IORef
import System.IO.Unsafe

import Data.Kind
import qualified GHC.Generics as GHC
import Generics.SOP
import Generics.SOP.NP
import Generics.SOP.Constraint
import Control.DeepSeq


--------------------------------------------------------
-- The basic types which make up a demand description --
--------------------------------------------------------

data Thunk a = E !a | T
  deriving (Eq, Ord, Show, Functor, GHC.Generic, NFData)


-------------------------------------------------------------
-- For brevity, some abbreviations for repeated signatures --
-------------------------------------------------------------

data PrettyDemand string =
  Constr string
    (Either [Thunk (PrettyDemand string)]
            [(string, Thunk (PrettyDemand string))])
  deriving (Eq, Ord, Show)

instance Functor PrettyDemand where
  fmap f (Constr name (Left thunks)) =
    Constr (f name) (Left $ fmap (fmap (fmap f)) thunks)
  fmap f (Constr name (Right fields)) =
    Constr (f name)
           (Right $ (fmap (\(a, thunk) -> (f a, fmap (fmap f) thunk))) fields)


---------------------------
-- The Observe typeclass --
---------------------------

class Functor1 h where
  fmap1 :: (forall x. f x -> g x) -> h f -> h g

class (Functor1 (Demand a)) => Observe (a :: *) where
  type Demand a :: (* -> *) -> *
  type Demand a = GDemand a

  projectD :: (forall x. Observe x => x -> f x) -> a -> Demand a f
  default projectD :: GObserve a
                   => (forall x. Observe x => x -> f x)
                   -> a -> Demand a f
  projectD = gProjectD

  embedD   :: (forall x. Observe x => f x -> x) -> Demand a f -> a
  default embedD :: GObserve a
                 => (forall x. Observe x => f x -> x)
                 -> Demand a f -> a
  embedD = gEmbedD

  -- zipD     :: (forall x. f x -> g x -> h x) -> Demand a f -> Demand a g -> Demand a h
  -- unzipD   :: (forall x. h x -> (f x, g x)) -> Demand a h -> (Demand a f, Demand a g)

-- TODO: reintroduce HFunctor, make Field one
newtype Field (f :: * -> *) (a :: *) :: * where
  Field :: f (Demand a (Field f)) -> Field f a

deriving instance (Show (f (Demand a (Field f)))) => Show (Field f a)

newtype GDemand a f =
  GD (NS (NP f) (Code a))

type GObserve a =
  ( Generic a
  , Demand a ~ GDemand a
  , All2 Observe (Code a)
  , SListI (Code a)
  , AllF SListI (Code a)
  )

instance (SListI (Code a), AllF SListI (Code a)) => Functor1 (GDemand a) where
  fmap1 t (GD sop) =
    GD $ unSOP $ hliftA t (SOP sop)

gProjectD :: GObserve a
          => (forall x. Observe x => x -> f x)
          -> a -> Demand a f
gProjectD p a =
  GD (unSOP (hcliftA (Proxy :: Proxy Observe) (p . unI) (from a)))

gEmbedD :: GObserve a
        => (forall x. Observe x => f x -> x)
        -> Demand a f -> a
gEmbedD e (GD d) =
  to (hcliftA (Proxy :: Proxy Observe) (I . e) (SOP d))

deriving instance GHC.Generic (GDemand a f)
deriving instance ( SListI (Code a)
                  , AllF (Compose Eq (NP f)) (Code a)
                  ) => Eq (GDemand a f)
deriving instance ( SListI (Code a)
                  , AllF (Compose Eq (NP f)) (Code a)
                  , AllF (Compose Ord (NP f)) (Code a)
                  ) => Ord (GDemand a f)
deriving instance ( SListI (Code a)
                  , AllF (Compose Show (NP f)) (Code a)
                  ) => Show (GDemand a f)
deriving instance ( SListI (Code a)
                  , AllF (Compose NFData (NP f)) (Code a)
                  ) => NFData (GDemand a f)


type family Demands

instance Observe () where
  projectD _ _ = GD (Z Nil)
  embedD   _ _ = ()

instance (Observe a, Observe b) => Observe (a, b) where
  projectD p (a, b) = GD (Z (p a :* p b  :* Nil))
  embedD   e (GD (Z (fa :* fb  :* Nil))) = (e fa, e fb)

projectField :: forall a f. Observe a
             => (forall x. x -> f x)
             -> a -> Field f a
projectField p a =
  Field (p (projectDemand a))
    where
      projectDemand :: a -> Demand a (Field f)
      projectDemand a' = projectD (projectField p) a'

embedField :: forall a f. Observe a
           => (forall x. f x -> x)
           -> Field f a -> a
embedField e (Field d) =
  embedDemand (e d)
  where
    embedDemand :: Demand a (Field f) -> a
    embedDemand d' = embedD (embedField e) d'

-- foldD :: forall a f g. Observe a
--       => (forall x h. Demand x h -> g x)
--       -> Demand a f -> g a

-- instance Observe () where
--   type Demand () = Proxy
--   mapD     _ _   = Proxy
--   projectD _ _   = Proxy
--   embedD   _ _   = ()

-- instance (Observe a, Observe b) => Observe (Either a b) where
--   mapD f (L a) = L (mapD @a f a)
--   mapD f (R b) = R (mapD @b f b)
--   projectD p (Left a)  = L (projectD p a)
--   projectD p (Right b) = R (projectD p b)
--   embedD e (L a) = Left  (embedD e a)
--   embedD e (R b) = Right (embedD e b)


------------------------------------------------------
-- Observing demand behavior of arbitrary functions --
------------------------------------------------------

-- | Force a value in some applicative context. This is useful for ensuring that
-- values are evaluated in the correct order inside of unsafePerformIO blocks.
evaluate :: Applicative f => a -> f ()
evaluate !_ = pure ()


---------------------------------------------------
-- Generic implementation of the Observe methods --
---------------------------------------------------
