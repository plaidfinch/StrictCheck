{-# language DataKinds, GADTs, BangPatterns, TypeFamilies, RankNTypes,
  AllowAmbiguousTypes, UndecidableInstances, DefaultSignatures,
  TypeApplications, ScopedTypeVariables, FlexibleContexts, ConstraintKinds,
  DeriveFunctor, FlexibleInstances, StandaloneDeriving, DeriveGeneric,
  DeriveAnyClass, TypeOperators, PolyKinds, DeriveDataTypeable,
  PartialTypeSignatures #-}

{-# OPTIONS_GHC -fno-warn-unused-imports #-}
{-# OPTIONS_GHC -fno-warn-partial-type-signatures #-}

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


---------------------------
-- The Observe typeclass --
---------------------------

class Typeable a => Observe (a :: *) where
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
    => (forall x. Observe x => x -> f x) -> a -> Demand a f
  projectD = gProjectD

  embedD :: (forall x. Observe x => f x -> x) -> Demand a f -> a
  default embedD :: GObserve a
    => (forall x. Observe x => f x -> x) -> Demand a f -> a
  embedD = gEmbedD


-----------------------------------------------
-- Introducing recursion into demands: Field --
-----------------------------------------------

newtype Field (f :: * -> *) (a :: *) :: * where
  F :: f (Demand a (Field f)) -> Field f a

unF :: Field f a -> f (Demand a (Field f))
unF (F df) = df

foldD :: forall a f g. (Functor f, Observe a)
      => (forall x. Observe x => f (Demand x g) -> g x)
      -> Field f a -> g a
foldD alg = alg . fmap (mapD @a (foldD alg)) . unF

unfoldD :: forall a f g. (Functor g, Observe a)
        => (forall x. Observe x => f x -> g (Demand x f))
        -> f a -> Field g a
unfoldD coalg = F . fmap (mapD @a (unfoldD coalg)) . coalg

projectField :: forall a f. (Functor f, Observe a)
             => (forall x. x -> f x)
             -> a -> Field f a
projectField p = unfoldD (fmap (projectD p)) . p

embedField :: forall a f. (Functor f, Observe a)
           => (forall x. f x -> x)
           -> Field f a -> a
embedField e = e . foldD (fmap (embedD e))

unzipField :: forall a f g h.
           (Observe a, Functor f, Functor g, Functor h)
           => (forall x. f x -> (g x, h x))
           -> Field f a -> (Field g a, Field h a)
unzipField split =
  getBoth . foldD (Both . crunch . split)
  where
    crunch :: forall x. Observe x
           => (g _, h _) -> (Field g x, Field h x)
    crunch =
      bimap (F . fmap (mapD @x fstBoth))
            (F . fmap (mapD @x sndBoth))


-----------------------------
-- The Both type is useful --
-----------------------------

newtype Both f g a = Both (f a, g a)

getBoth :: Both f g a -> (f a, g a)
getBoth (Both both) = both

fstBoth :: Both f g a -> f a
fstBoth (Both (fa, _)) = fa

sndBoth :: Both f g a -> g a
sndBoth (Both (_, ga)) = ga


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
                  !_ <- evaluate a
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
    !_ <- evaluate (context result)
    !_ <- evaluate (rnf observation)
    return (result, observation)

-- TODO: Implement n-ary observation


-----------------------------
-- Pretty-printing demands --
-----------------------------

data PrettyDemand string a =
  Constr string
    (Either [Thunk a]
            [(string, Thunk a)])
  deriving (Eq, Ord, Show)

instance Functor (PrettyDemand string) where
  fmap = second

instance Bifunctor PrettyDemand where
  first f (Constr    name  (Left fields)) =
           Constr (f name) (Left fields)
  first f (Constr    name (Right fields)) =
           Constr (f name) (Right $ (fmap (first f)) fields)
  second f (Constr name (Left fields)) =
            Constr name (Left $ (fmap (fmap f)) fields)
  second f (Constr name (Right fields)) =
            Constr name (Right $ fmap (second (fmap f)) fields)


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


--------------------------------------
-- Deriving instances for things... --
--------------------------------------

deriving instance GHC.Generic (Field f a)
deriving instance (Eq     (f (Demand a (Field f)))) => Eq     (Field f a)
deriving instance (Ord    (f (Demand a (Field f)))) => Ord    (Field f a)
deriving instance (Show   (f (Demand a (Field f)))) => Show   (Field f a)
deriving instance (NFData (f (Demand a (Field f)))) => NFData (Field f a)

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
