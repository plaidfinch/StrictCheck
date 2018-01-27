{-# language DataKinds, GADTs, BangPatterns, TypeFamilies, RankNTypes,
  AllowAmbiguousTypes, UndecidableInstances, DefaultSignatures,
  TypeApplications, ScopedTypeVariables, FlexibleContexts, ConstraintKinds,
  DeriveFunctor, FlexibleInstances, StandaloneDeriving, DeriveGeneric,
  DeriveAnyClass, TypeOperators, PolyKinds, DeriveDataTypeable,
  PartialTypeSignatures, LambdaCase #-}

{-# OPTIONS_GHC -fno-warn-unused-imports #-}
--{-# OPTIONS_GHC -fno-warn-partial-type-signatures #-}

module Test.StrictCheck.Observe where

import Control.Exception hiding ( evaluate )
-- import Data.Typeable
import Data.IORef
import System.IO.Unsafe

import Data.Kind
import qualified GHC.Generics as GHC
import Generics.SOP
import Generics.SOP.NP
import Generics.SOP.NS
import Generics.SOP.Constraint
import Control.DeepSeq
import Data.Bifunctor
import Control.Monad.Identity
import Data.Fix
import Type.Reflection
import Data.Functor.Product
import Unsafe.Coerce
import Data.List.NonEmpty


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

  projectD :: (forall x. Observe x => x -> f x) -> a -> Demand a f
  default projectD :: GObserve a
    => (forall x. Observe x => x -> f x) -> a -> Demand a f
  projectD = gProjectD

  embedD :: (forall x. Observe x => f x -> x) -> Demand a f -> a
  default embedD :: GObserve a
    => (forall x. Observe x => f x -> x) -> Demand a f -> a
  embedD = gEmbedD

  withFieldsD
    :: Demand a f
    -> (forall xs. All Observe xs
          => NP f xs
          -> (forall g. NP g xs -> Demand a g)
          -> result)
    -> result
  default withFieldsD
    :: GObserve a
    => Demand a f
    -> (forall xs. All Observe xs
          => NP f xs
          -> (forall g. NP g xs -> Demand a g)
          -> result)
    -> result
  withFieldsD = gWithFieldsD

  matchD :: (forall x. f x -> g x -> h x)
         -> Demand a f -> Demand a g -> Maybe (Demand a h)
  default matchD :: GObserve a
    => (forall x. f x -> g x -> h x)
    -> Demand a f -> Demand a g -> Maybe (Demand a h)
  matchD = gMatchD

  -- prettyD :: Demand a g
  --         -> [PrettyDemand f QConstructorName]
  --         -> PrettyDemand f QConstructorName
  -- default prettyD :: (GObserve a, HasDatatypeInfo a)
  --   => Demand a f
  --   -> [PrettyDemand f QConstructorName]
  --   -> PrettyDemand f QConstructorName
  -- prettyD = gPrettyD

-- TODO: Put the stuff below here somewhere else

mapD :: forall a f g. Observe a
      => (forall x. Observe x => f x -> g x)
      -> Demand a f -> Demand a g
mapD t d = withFieldsD @a d $ \fields unflatten ->
  unflatten (hcliftA (Proxy :: Proxy Observe) t fields)

withFieldsViaList :: forall f demand result.
     (forall r h.
        demand h ->
        (forall x. Observe x
           => [f x]
           -> (forall g. [g x] -> demand g)
           -> r)
        -> r)
  -> demand f
  -> (forall xs. All Observe xs
        => NP f xs
        -> (forall g. NP g xs -> demand g)
        -> result)
  -> result
withFieldsViaList viaList demand cont =
  viaList demand $
    \list unflatten ->
       withNP @Observe list unflatten cont

withNP :: forall c demand result f x. c x
       => [f x]
       -> (forall g. [g x] -> demand g)
       -> (forall xs. All c xs
             => NP f xs -> (forall g. NP g xs -> demand g) -> result)
       -> result
withNP list unList cont =
  withUnhomogenized @c list $ \np ->
    cont np (unList . homogenize)

homogenize :: All ((~) a) as => NP f as -> [f a]
homogenize      Nil  = []
homogenize (a :* as) = a : homogenize as

withUnhomogenized :: forall c a f r.
  c a => [f a] -> (forall as. (All c as, All ((~) a) as) => NP f as -> r) -> r
withUnhomogenized      []  k = k Nil
withUnhomogenized (a : as) k =
  withUnhomogenized @c as $ \np -> k (a :* np)

shrinkField :: forall a. Observe a => Field Thunk a -> [Field Thunk a]
shrinkField (F T)     = []
shrinkField (F (E d)) =
  withFieldsD @a d $ \np unflat ->
    case shrinkOne np of
      [] -> [F T]
      xs -> fmap (F . E . unflat) xs
  where
    shrinkOne :: All Observe xs => NP (Field Thunk) xs -> [NP (Field Thunk) xs]
    shrinkOne Nil = []
    shrinkOne (F T :* xs) =
      (F T :*) <$> shrinkOne xs
    shrinkOne (f@(F (E _)) :* xs) =
      fmap (:* xs) (shrinkField f) ++ fmap (f :* ) (shrinkOne xs)


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

-- TODO: mapMD, foldMD, unfoldMD, ...

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
           => (forall x. f x -> Product g h x)
           -> Field f a -> Product (Field g) (Field h) a
unzipField split =
  foldD (crunch . split)
  where
    crunch :: forall x. Observe x
           => Product g h (Demand x (Product (Field g) (Field h)))
           -> Product (Field g) (Field h) x
    crunch =
      uncurry Pair
      . bimap (F . fmap (mapD @x (\(Pair l _) -> l)))
              (F . fmap (mapD @x (\(Pair _ r) -> r)))
      . (\(Pair l r) -> (l, r))

-- prettyField :: forall a f. (Observe a, Functor f) => Field f a
--             -> f (Fix (PrettyDemand f QConstructorName))
-- prettyField = unK . foldD oneLevel
--   where
--     oneLevel :: forall x. Observe x
--              => f (Demand x (K (f (Fix (PrettyDemand f QConstructorName)))))
--              -> K (f (Fix (PrettyDemand f QConstructorName))) x
--     oneLevel = K . fmap @f (Fix . prettyD @x)


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
    return ( (unsafePerformIO $ do
                writeIORef ref (E a)
                return a)
           , unsafePerformIO (readIORef ref) )

{-# NOINLINE entangleField #-}
entangleField :: Observe a => a -> (a, Field Thunk a)
entangleField =
  first (embedField unI)
  . (\(Pair l r) -> (l, r))
  . unzipField (uncurry Pair . first I . entangle . unI)
  . projectField I

observe :: (Observe a, NFData (Demand a (Field Thunk)))
        => (b -> ()) -> (a -> b) -> a -> (b, Field Thunk a)
observe context function input =
  runIdentity $ do
    let (observable, observation) = entangleField input
        result = function observable
    !_ <- evaluate (context result)
    !_ <- evaluate (rnf observation)
    return (result, observation)

-- TODO: Implement n-ary observation


-----------------------------
-- Pretty-printing demands --
-----------------------------

-- data PrettyDemand f string =
--     Algebraic string (Either [f (PrettyDemand f string)]
--                            [(string, f (PrettyDemand f string))])
--   | Abstract string [Either String (Int, f (PrettyDemand f string))]
--   deriving (Eq, Ord, Show)

-- instance Functor f => Functor (PrettyDemand f string) where
--   fmap = second

-- instance Functor f => Bifunctor (PrettyDemand f) where
--   first f (Constr    name  (Left fields)) =
--            Constr (f name) (Left fields)
--   first f (Constr    name (Right fields)) =
--            Constr (f name) (Right $ (fmap (first f)) fields)
--   second f (Constr name (Left fields)) =
--             Constr name (Left $ (fmap (fmap f)) fields)
--   second f (Constr name (Right fields)) =
--             Constr name (Right $ fmap (second (fmap f)) fields)

type QConstructorName = (ModuleName, DatatypeName, ConstructorName)

-- TODO: More flexible pretty-type, to allow abstract types to be correctly
-- represented and displayed. This will require capturing info about
-- associativity and fixity.

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
  , All SListI (Code a) )

-- gMapD :: GObserve a
--       => (forall x. Observe x => f x -> g x)
--       -> Demand a f -> Demand a g
-- gMapD t (GD sop) =
--   GD $ unSOP $ hcliftA (Proxy :: Proxy Observe) t (SOP sop)

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

gWithFieldsD :: forall a f result. GObserve a
  => Demand a f
  -> (forall xs. All Observe xs
        => NP f xs
        -> (forall g. NP g xs -> Demand a g)
        -> result)
  -> result
gWithFieldsD (GD d) cont =
  go d (\fields unflatten -> cont fields (GD . unflatten))
  where
    go :: forall xss r.
      (All SListI xss, All2 Observe xss)
       => NS (NP f) xss
       -> (forall xs. All Observe xs =>
             (NP f xs -> (forall g. NP g xs -> NS (NP g) xss) -> r))
       -> r
    go (Z fields) k = k fields Z
    go (S more)   k =
      go more $ \fields unflatten ->
        k fields (S . unflatten)

gMatchD :: forall a f g h. GObserve a
        => (forall x. f x -> g x -> h x)
        -> Demand a f -> Demand a g
        -> Maybe (Demand a h)
gMatchD combine (GD df) (GD dg) =
  GD <$> go df dg
  where
    go :: forall xss. All SListI xss
       => NS (NP f) xss
       -> NS (NP g) xss
       -> Maybe (NS (NP h) xss)
    go (Z fs)  (Z gs)  = Just (Z (liftA2_NP combine fs gs))
    go (S fss) (S gss) = S <$> go fss gss
    go _       _       = Nothing

-- gPrettyD :: forall a x f. (HasDatatypeInfo a, GObserve a)
--          => Demand a (K (f x))
--          -> PrettyDemand f QConstructorName x
-- gPrettyD (GD demand) =
--   case info of
--     ADT m d cs ->
--       prettyC m d demand cs
--     Newtype m d c ->
--       prettyC m d demand (c :* Nil)
--   where
--     info = datatypeInfo (Proxy :: Proxy a)

--     prettyC :: forall as. ModuleName -> DatatypeName
--             -> NS (NP (K (f x))) as
--             -> NP ConstructorInfo as
--             -> PrettyDemand f QConstructorName x
--     prettyC m d subDemand constructors =
--       case (subDemand, constructors) of
--         (Z demandFields, c :* _) ->
--           case c of
--             Constructor name ->
--               Constr (m, d, name) . Left $
--                 hcollapse demandFields
--             Infix name _ _ ->
--               Constr (m, d, name) . Left $
--                 hcollapse demandFields
--             Record name fieldsInfo ->
--               Constr (m, d, name) . Right $
--                 zip ( hcollapse
--                     . hliftA (\(FieldInfo f) -> K (m, d, f))
--                     $ fieldsInfo )
--                     (hcollapse demandFields)
--         (S another, _ :* different) ->
--           prettyC m d another different

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
                  , All (Compose Eq (NP f)) (Code a)
                  ) => Eq (GDemand a f)
deriving instance ( SListI (Code a)
                  , All (Compose Eq (NP f)) (Code a)
                  , All (Compose Ord (NP f)) (Code a)
                  ) => Ord (GDemand a f)
deriving instance ( SListI (Code a)
                  , All (Compose Show (NP f)) (Code a)
                  ) => Show (GDemand a f)
deriving instance ( SListI (Code a)
                  , All (Compose NFData (NP f)) (Code a)
                  ) => NFData (GDemand a f)
