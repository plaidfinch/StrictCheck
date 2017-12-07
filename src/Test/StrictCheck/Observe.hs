{-# language DataKinds, GADTs, BangPatterns, TypeFamilies, RankNTypes,
  AllowAmbiguousTypes, UndecidableInstances, DefaultSignatures,
  TypeApplications, ScopedTypeVariables, FlexibleContexts, ConstraintKinds,
  DeriveFunctor, FlexibleInstances, StandaloneDeriving, DeriveGeneric,
  DeriveAnyClass, TypeOperators #-}

module Test.StrictCheck.Observe where

import Data.IORef
import System.IO.Unsafe

import Data.Kind ( Type )
import qualified GHC.Generics as GHC
import Generics.SOP
import Generics.SOP.NP
import Generics.SOP.Constraint
import Control.DeepSeq


--------------------------------------------------------
-- The basic types which make up a demand description --
--------------------------------------------------------

data DemandKind = Observing | Describing

data Thunk a = E !a | T
  deriving (Eq, Ord, Show, Functor, GHC.Generic, NFData)

data Field (t :: DemandKind) (a :: Type) where
  F ::        Thunk (Demand a 'Describing) -> Field 'Describing a
  R :: IORef (Thunk (Demand a 'Observing)) -> Field 'Observing  a

unF :: Field 'Describing a -> Thunk (Demand a 'Describing)
unF (F t) = t

instance Show (Demand a 'Describing) => Show (Field 'Describing a) where
  showsPrec d (F t) =
    showParen (d > 10) $ showString "F " . showsPrec 11 t

instance NFData (Demand a 'Describing) => NFData (Field 'Describing a) where
  rnf (F t) = rnf t


-------------------------------------------------------------
-- For brevity, some abbreviations for repeated signatures --
-------------------------------------------------------------

type family Demands (ts :: [Type]) (d :: DemandKind) :: [Type] where
  Demands     '[]  d = '[]
  Demands (t : ts) d = Demand t d : Demands ts d

type Observation a t =
  (forall x. Observe x => x -> (x, Field t x))
  -> a -> (a, Demand a t)

type Reification a s t =
  (forall x. Observe x => Field s x -> Field t x)
   -> Demand a s -> Demand a t

type Forcing a t =
  (forall x. Observe x => Field t x -> x -> ())
   -> Demand a t -> a -> ()

type Prettying a t =
  (forall x. Observe x => Field t x -> Thunk (PrettyDemand String))
  -> Demand a t -> PrettyDemand String

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

class Observe (a :: Type) where
  type Demand a :: DemandKind -> Type
  type Demand a = GDemand a

  observe :: Observation a t
  default observe :: GenericObserve a => Observation a t
  observe = gObserve

  reify :: Reification a s t
  default reify :: GenericObserve a => Reification a s t
  reify = gReify

  force :: Forcing a t
  default force :: GenericObserve a => Forcing a t
  force = gForce

  pretty :: Prettying a t
  default pretty :: (GenericObserve a, HasDatatypeInfo a) => Prettying a t
  pretty = gPretty


------------------------------------------------------
-- Observing demand behavior of arbitrary functions --
------------------------------------------------------

data PairWithField (d :: DemandKind) x =
  PWF x (Field d x)

unPWF :: PairWithField d x -> (I x, Field d x)
unPWF (PWF x fx) = (I x, fx)

data ThunkDemand (d :: DemandKind) x =
  TD (Thunk (Demand x d))

unwrapTDs :: NP (ThunkDemand d) xs -> NP Thunk (Demands xs d)
unwrapTDs         Nil  = Nil
unwrapTDs (TD x :* xs) = x :* unwrapTDs xs

unzipWith_NP :: (forall x. f x -> (g x, h x))
             -> NP f xs -> (NP g xs, NP h xs)
unzipWith_NP _            Nil  = (Nil, Nil)
unzipWith_NP perElem (x :* xs) =
  let (y, z)   = perElem x
      (ys, zs) = unzipWith_NP perElem xs
  in (y :* ys, z :* zs)

-- | Given a context, function, and input, calculate the output of the function,
-- the demand placed on that output by the context, and the demand induced on
-- its input by that output demand. This is referentially transparent.
observeDemand :: forall inputs output.
              (All Observe inputs, Observe output,
               All NFData (Demands inputs 'Describing ),
               NFData (Demand output 'Describing))
       => (output -> ()) -> (NP I inputs -> output) -> NP I inputs
       -> (output, (NP Thunk (Demands inputs 'Describing),
                       Thunk (Demand  output 'Describing)))
observeDemand context f inputs =
  unsafePerformIO $ do
    let output = f observableInputs
        (observableInputs, inputDemandsMutable) =
          unzipWith_NP unPWF $ cmap_NP pObserve (instrument . unI) inputs
        (I observableOutput, outputDemandMutable) =
          unPWF $ instrument output
        inputDemands = unwrapTDs $
          cmap_NP pObserve (TD . unF . freeze) inputDemandsMutable
        F outputDemand = freeze outputDemandMutable
    evaluate (context observableOutput)
    evaluate (rnfThunks inputDemands)
    evaluate (rnf outputDemand)
    return (output, (inputDemands, outputDemand))
  where
    pObserve = Proxy :: Proxy Observe
    pNFData  = Proxy :: Proxy NFData

    rnfThunks :: All NFData xs => NP Thunk xs -> ()
    rnfThunks = unK . ccata_NP pNFData (K ())
                      (\fy kys -> K (rnf fy `seq` rnf kys))

    {-# NOINLINE instrument #-}
    instrument :: forall x. Observe x => x -> PairWithField 'Observing x
    instrument x =
      unsafePerformIO $ do
        ref <- newIORef T
        return $ PWF (unsafePerformIO $ do
                        let (x', demandX) =
                              observe ((\(I a, fa) -> (a, fa))
                                       . unPWF . instrument) x
                        writeIORef ref (E demandX)
                        return x')
                     (R ref)

    {-# NOINLINE freeze #-}
    freeze :: forall x. Observe x => Field 'Observing x -> Field 'Describing x
    freeze (R ref) =
      F . fmap (reify @x freeze) . unsafePerformIO $ readIORef ref

-- | Force a value in some applicative context. This is useful for ensuring that
-- values are evaluated in the correct order inside of unsafePerformIO blocks.
evaluate :: Applicative f => a -> f ()
evaluate !_ = pure ()

-- | Given an observable piece of data, construct the demand corresponding to
-- a full evaluation of that value. This has no instrumentation overhead.
demandShape :: Observe a => a -> Demand a 'Describing
demandShape = snd . observe (\x -> (x, F . E . demandShape $ x))

-- | Convert a demand into a monomorphic tree data structure with enough info
-- to format it in a variety of ways for human consumption.
prettyDemandTree :: forall a. Observe a
                 => Demand a 'Describing -> PrettyDemand String
prettyDemandTree demand =
  pretty @a prettyField demand
  where
    prettyField :: forall x. Observe x
                => Field 'Describing x -> Thunk (PrettyDemand String)
    prettyField (F T)     = T
    prettyField (F (E d)) = E (prettyDemandTree @x d)


---------------------------------------------------
-- Generic implementation of the Observe methods --
---------------------------------------------------

newtype GDemand a t =
  GD (NS (NP (Field t)) (Code a))
  deriving (GHC.Generic)

deriving instance ( SListI (Code a)
                  , AllF (Compose Eq (NP (Field 'Describing))) (Code a)
                  ) => Eq (GDemand a 'Describing)
deriving instance ( SListI (Code a)
                  , AllF (Compose Eq (NP (Field 'Describing))) (Code a)
                  , AllF (Compose Ord (NP (Field 'Describing))) (Code a)
                  ) => Ord (GDemand a 'Describing)
deriving instance ( SListI (Code a)
                  , AllF (Compose Show (NP (Field 'Describing))) (Code a)
                  ) => Show (GDemand a 'Describing)
deriving instance ( SListI (Code a)
                  , AllF (Compose NFData (NP (Field 'Describing))) (Code a)
                  ) => NFData (GDemand a 'Describing)

type GenericObserve a =
  (Generic a, Demand a ~ GDemand a, All (All Observe) (Code a))


gObserve :: forall a t. GenericObserve a => Observation a t
gObserve observeF a =
  let (repA', dA) = observeSum (unSOP (from a))
  in (to (SOP repA'), GD dA)
  where
    observeSum ::
      forall xss. All (All Observe) xss
        =>  NS (NP I) xss
        -> (NS (NP I) xss, NS (NP (Field t)) xss)
    observeSum rep =
      case rep of
        Z cons ->
          let (results, demands) = observeProd cons
          in (Z results, Z demands)
        S next ->
          let (results, demands) = observeSum next
          in (S results, S demands)

    observeProd :: forall xs. All Observe xs
             =>  (NP I) xs
             -> ((NP I) xs, NP (Field t) xs)
    observeProd Nil = (Nil, Nil)
    observeProd (I x :* xs) =
      let (results, demands) = observeProd xs
          (result,  demand)  = observeF x
      in (I result :* results, demand :* demands)

gReify :: forall a s t. GenericObserve a => Reification a s t
gReify reifyF (GD demand) =
  GD $ reifySum demand
  where
    reifySum ::
      forall xss. All (All Observe) xss
        => NS (NP (Field s)) xss
        -> NS (NP (Field t)) xss
    reifySum (Z cons) = Z $ reifyProd cons
    reifySum (S next) = S $ reifySum next

    reifyProd :: forall xs. All Observe xs
             => NP (Field s) xs
             -> NP (Field t) xs
    reifyProd Nil       = Nil
    reifyProd (f :* fs) = reifyF f :* reifyProd fs

gForce :: forall a t. GenericObserve a => Forcing a t
gForce forceF (GD demand) a =
  forceSum demand (unSOP $ from a)
  where
    forceSum :: forall xss. All (All Observe) xss
             => NS (NP (Field t)) xss -> NS (NP I) xss -> ()
    forceSum sumDemand value =
      case (sumDemand, value) of
        (Z prodDemand, Z fields) -> forceProd prodDemand fields
        (S sumDemand', S value') -> forceSum  sumDemand' value'
        (Z _, S _) -> ()
        (S _, Z _) -> ()

    forceProd :: forall xs. All Observe xs
              => NP (Field t) xs -> NP I xs -> ()
    forceProd Nil Nil = ()
    forceProd (d :* ds) (I x :* xs) =
      case (forceF d x, forceProd ds xs) of
        ((), ()) -> ()

gPretty :: forall a t. (GenericObserve a, HasDatatypeInfo a)
        => Prettying a t
gPretty prettyF (GD demand) =
  prettySum demand (constructorInfo $ datatypeInfo (Proxy :: Proxy a))
  where
    prettySum :: forall xss. All (All Observe) xss
              => NS (NP (Field t)) xss
              -> NP ConstructorInfo xss
              -> PrettyDemand String
    prettySum (S sums)   (_  :* cis) = prettySum sums cis
    prettySum (Z fields) (ci :* _) =
      case ci of
        Constructor name ->
          Constr name (Left (prettyProd fields))
        Infix name _ _ ->
          Constr name (Left (prettyProd fields))
        Record name fieldNames ->
          Constr name (Right $ zip (listFieldNames fieldNames)
                                   (prettyProd fields))

    prettyProd :: forall xs. All Observe xs
               => NP (Field t) xs -> [Thunk (PrettyDemand String)]
    prettyProd Nil = []
    prettyProd (f :* fs) =
      prettyF f : prettyProd fs

    listFieldNames :: NP FieldInfo xs -> [String]
    listFieldNames Nil = []
    listFieldNames (FieldInfo name :* fieldNames) =
      name : listFieldNames fieldNames
