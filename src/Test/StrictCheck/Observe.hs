{-# language DataKinds, GADTs, BangPatterns, TypeFamilies, RankNTypes,
  AllowAmbiguousTypes, UndecidableInstances, DefaultSignatures,
  TypeApplications, ScopedTypeVariables, FlexibleContexts, ConstraintKinds,
  DeriveFunctor, FlexibleInstances, StandaloneDeriving, DeriveGeneric,
  DeriveAnyClass, TypeOperators, PolyKinds, DeriveDataTypeable #-}

{-# OPTIONS_GHC -fno-warn-unused-imports #-}

module Test.StrictCheck.Observe where

import Control.Exception hiding ( evaluate )
import Data.Typeable
import Data.IORef
import System.IO.Unsafe

import Data.Kind
import qualified GHC.Generics as GHC
import Generics.SOP
import Generics.SOP.NP
import Generics.SOP.Constraint
import Control.DeepSeq
import Data.Bifunctor
import Control.Monad.Identity


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

class Observe (a :: *) where
  type Demand a :: (* -> *) -> *
  type Demand a = GDemand a

  mapD :: (forall x. Observe x => f x -> g x)
       -> Demand a f -> Demand a g
  default mapD :: GObserve a
               => (forall x. Observe x => f x -> g x)
               -> Demand a f -> Demand a g
  mapD = gMapD

  projectD :: (forall x. Observe x => x -> f x) -> a -> Demand a f
  default projectD :: GObserve a
                   => (forall x. Observe x => x -> f x)
                   -> a -> Demand a f
  projectD = gProjectD

  embedD :: (forall x. Observe x => f x -> x) -> Demand a f -> a
  default embedD :: GObserve a
                 => (forall x. Observe x => f x -> x)
                 -> Demand a f -> a
  embedD = gEmbedD

  unzipD :: (forall x. Observe x => f x -> (g x, h x))
         -> Demand a f -> (Demand a g, Demand a h)
  default unzipD :: GObserve a
                 => (forall x. Observe x => f x -> (g x, h x))
                 -> Demand a f -> (Demand a g, Demand a h)
  unzipD = gUnzipD

newtype Field (f :: * -> *) (a :: *) :: * where
  F :: f (Demand a (Field f)) -> Field f a

deriving instance GHC.Generic (Field f a)
deriving instance (Eq     (f (Demand a (Field f)))) => Eq     (Field f a)
deriving instance (Ord    (f (Demand a (Field f)))) => Ord    (Field f a)
deriving instance (Show   (f (Demand a (Field f)))) => Show   (Field f a)
deriving instance (NFData (f (Demand a (Field f)))) => NFData (Field f a)

projectField :: forall a f. Observe a
             => (forall x. x -> f x)
             -> a -> Field f a
projectField p a =
  F (p (projectD (projectField p) a))

embedField :: forall a f. Observe a
           => (forall x. f x -> x)
           -> Field f a -> a
embedField e (F d) =
  embedD (embedField e) (e d)

unzipField :: forall a f g h.
           (Observe a, Functor f, Functor g, Functor h)
           => (forall x. f x -> (g x, h x))
           -> Field f a -> (Field g a, Field h a)
unzipField split (F df) =
  let (dg, dh) =
        split (unzipD @a (unzipField split) <$> df)
  in (F (fmap fst dg), F (fmap snd dh))


-- | Convenience type for representing demands upon abstract structures with one
-- type recursively-demanded type parameter (i.e. (Map k) or Seq)

newtype WithFieldsOf h a f = WFO (h (f a))

mapWFO :: (Functor h, Observe a)
       => (forall x. Observe x => f x -> g x)
       -> WithFieldsOf h a f
       -> WithFieldsOf h a g
mapWFO t (WFO x) = WFO (fmap t x)

projectWFO :: (Functor h, Observe a)
           => (forall x. Observe x => x -> f x)
           -> h a -> WithFieldsOf h a f
projectWFO p a = WFO (fmap p a)

embedWFO :: (Functor h, Observe a)
         => (forall x. Observe x => f x -> x)
         -> WithFieldsOf h a f -> h a
embedWFO e (WFO m) = fmap e m

-- foldD :: forall a f g. Observe a
--       => (forall x h. Demand x h -> g x)
--       -> Demand a f -> g a


------------------------------------------------------
-- Observing demand behavior of arbitrary functions --
------------------------------------------------------

-- | Force a value in some applicative context. This is useful for ensuring that
-- values are evaluated in the correct order inside of unsafePerformIO blocks.
evaluate :: Applicative f => a -> f ()
evaluate !_ = pure ()

{-# NOINLINE entangle #-}
entangle :: forall a. a -> (a, Thunk a)
entangle a =
  unsafePerformIO $ do
    ref <- newIORef T
    return . unsafePerformIO $ do
      return ( (unsafePerformIO $ do
                  evaluate a
                  writeIORef ref (E a)
                  return a)
            , unsafePerformIO (readIORef ref) )

{-# NOINLINE entangleField #-}
entangleField :: Observe a => a -> (a, Field Thunk a)
entangleField =
  first (embedField unI)
  . unzipField (first I . entangle . unI)
  . projectField I

observe :: (Observe a, NFData (Demand a (Field Thunk)))
        => (b -> ()) -> (a -> b) -> a -> (b, Field Thunk a)
observe context function value =
  runIdentity $ do
    let (observable, observation) = entangleField value
        result = function observable
    evaluate (context result)
    evaluate (rnf observation)
    return (result, observation)


---------------------------------------------------
-- Generic implementation of the Observe methods --
---------------------------------------------------

newtype GDemand a f =
  GD (NS (NP f) (Code a))

type GObserve a =
  ( Generic a
  , Demand a ~ GDemand a
  , All2 Observe (Code a)
  , SListI (Code a)
  , AllF SListI (Code a) )

gMapD :: GObserve a
      => (forall x. Observe x => f x -> g x)
      -> Demand a f -> Demand a g
gMapD t (GD sop) =
  GD $ unSOP $ hcliftA (Proxy :: Proxy Observe) t (SOP sop)

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

gUnzipD :: forall a f g h. GObserve a
        => (forall x. Observe x => f x -> (g x, h x))
        -> Demand a f -> (Demand a g, Demand a h)
gUnzipD split (GD d) =
  let doubled =
        hcliftA (Proxy :: Proxy Observe) splitBoth (SOP d)
  in ( GD . unSOP $ hliftA fstBoth doubled
     , GD . unSOP $ hliftA sndBoth doubled )
  where
    splitBoth :: forall x. Observe x => f x -> Both g h x
    splitBoth fx = Both (split fx)

newtype Both f g a = Both (f a, g a)

fstBoth :: Both f g a -> f a
fstBoth (Both (fa, _)) = fa

sndBoth :: Both f g a -> g a
sndBoth (Both (_, ga)) = ga

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
