{-# language PartialTypeSignatures #-}
{-# OPTIONS_GHC -fno-warn-unused-imports #-}
{-# OPTIONS_GHC -fno-warn-partial-type-signatures #-}

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
import Data.Bifunctor.Flip
import Control.Monad.Identity
import Data.Fix
import Type.Reflection
import Data.Functor.Product
import Data.Constraint
import Text.Show
import Data.Monoid ( Endo(..) )
import Data.Void
import qualified Unsafe.Coerce as UNSAFE
import Data.Coerce

import Test.StrictCheck.Curry


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

  -- TODO: Derive matchD generically

  -- NOTE: new behavior should be to succeed whenever the same "constructor" was
  -- used -- either a literal constructor of a figurative one: map with exactly
  -- the same keys, *any* function considered same constructor...
  matchD :: Demand a f -> Demand a g
         -> (forall xs. All Observe xs
               => Flattened (Demand a) f xs
               -> Maybe (Flattened (Demand a) g xs)
               -> result)
         -> result
  default matchD :: GObserve a
         => Demand a f -> Demand a g
         -> (forall xs. All Observe xs
               => Flattened (Demand a) f xs
               -> Maybe (Flattened (Demand a) g xs)
               -> result)
         -> result
  matchD = gMatchD

  prettyD :: Demand a (K x) -> PrettyD x
  default prettyD :: (GObserve a, HasDatatypeInfo a)
          => Demand a (K x) -> PrettyD x
  prettyD = gPrettyD

data Flattened d f xs where
  Flattened
    :: (forall h. NP h xs -> d h)
    -> NP f xs
    -> Flattened d f xs

unflatten :: Flattened d f xs -> d f
unflatten (Flattened u p) = u p

mapFlattened :: forall c d f g xs. All c xs
  => (forall x. c x => f x -> g x) -> Flattened d f xs -> Flattened d g xs
mapFlattened t (Flattened u p) =
  Flattened u (hcliftA (Proxy :: Proxy c) t p)


-- TODO: Put the stuff below here somewhere else

mapD :: forall a f g. Observe a
      => (forall x. Observe x => f x -> g x)
      -> Demand a f -> Demand a g
mapD t d = matchD @a d d $ \flat _ ->
  unflatten $ mapFlattened @Observe t flat


shrinkField :: forall a. Observe a => Field Thunk a -> [Field Thunk a]
shrinkField (F T)     = []
shrinkField (F (E d)) =
  matchD @a d d $ \(Flattened un flat) _ ->
    case shrinkOne flat of
      [] -> [F T]
      xs -> fmap (F . E . un) xs
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

prettyField :: forall a f. (Observe a, Functor f)
  => Field f a -> PrettyField f
prettyField = unK . foldD oneLevel
  where
    oneLevel :: forall x. Observe x
             => f (Demand x (K (PrettyField f)))
             -> K (PrettyField f) x
    oneLevel = K . PF . fmap (prettyD @x)


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
    return ( unsafePerformIO $ do
               writeIORef ref (E a)
               return a
           , unsafePerformIO $ readIORef ref )

{-# NOINLINE entangleField #-}
entangleField :: Observe a => a -> (a, Field Thunk a)
entangleField =
  first (embedField unI)
  . (\(Pair l r) -> (l, r))
  . unzipField (uncurry Pair . first I . entangle . unI)
  . projectField I

observe1 :: (Observe a, Observe b, _)
         => (b -> ()) -> (a -> b) -> a -> (Field Thunk b, Field Thunk a)
observe1 context function input =
  runIdentity $ do
    let (input',  inputD)  = entangleField input
        (result', resultD) = entangleField (function input')
    !_ <- evaluate (context result')
    !_ <- evaluate (rnf inputD)
    !_ <- evaluate (rnf resultD)
    return (resultD, inputD)

observeNP :: (All Observe inputs, Observe result, _)
          => (result -> ())
          -> (NP I inputs -> result)
          -> NP I inputs
          -> ( Field Thunk result
             , NP (Field Thunk) inputs )
observeNP context function inputs =
  runIdentity $ do
    let entangled =
          hcliftA (Proxy :: Proxy Observe)
                  (uncurry Pair . first I . entangleField . unI) inputs
        (inputs', inputsD) =
          (hliftA (\(Pair r _) -> r) entangled,
           hliftA (\(Pair _ l) -> l) entangled)
        (result', resultD) = entangleField (function inputs')
    !_ <- evaluate (context result')
    !_ <- evaluate (rnf inputsD)
    !_ <- evaluate (rnf resultD)
    return (resultD, inputsD)

observe :: (All Observe (Args function), Observe (Result function), _)
        => (Result function -> ())
        -> function
        -> Args function
        ⋯-> ( Field Thunk (Result function)
             , NP (Field Thunk) (Args function) )
observe context function =
  curryAll (observeNP context (uncurryAll function))


-----------------------------
-- Pretty-printing demands --
-----------------------------

data PrettyD x = ConstructorD QName [x]
               | InfixD QName Associativity Fixity x x
               | RecordD QName [(QName, x)]
               | CustomD Fixity
                   [Either (Either String (ModuleName, String))
                           (Fixity, x)]
               deriving (Eq, Ord, Show, Functor)

newtype PrettyField f =
  PF (f (PrettyD (PrettyField f)))

deriving instance Eq   (f (PrettyD (PrettyField f))) => Eq   (PrettyField f)
deriving instance Ord  (f (PrettyD (PrettyField f))) => Ord  (PrettyField f)
deriving instance Show (f (PrettyD (PrettyField f))) => Show (PrettyField f)

type QName = (ModuleName, DatatypeName, String)

showPrettyFieldThunkS
  :: Bool -> String -> Int -> PrettyField Thunk -> String -> String
showPrettyFieldThunkS _            thunk _    (PF T)      = (thunk ++)
showPrettyFieldThunkS qualifyNames thunk prec (PF (E pd)) =
  case pd of
    ConstructorD name fields ->
      showParen (prec > 10 && length fields > 0) $
        showString (qualify name)
        . flip foldMapCompose fields
          (((' ' :) .) . showPrettyFieldThunkS qualifyNames thunk 11)
    RecordD name recfields ->
      showParen (prec > 10) $
        showString (qualify name)
        . flip foldMapCompose recfields
          (\(fName, x) ->
             ((((" " ++ qualify fName ++ " = ") ++) .) $
             showPrettyFieldThunkS qualifyNames thunk 11 x))
    InfixD name assoc fixity l r ->
      showParen (prec > fixity) $
        let (lprec, rprec) =
              case assoc of
                LeftAssociative  -> (fixity,     fixity + 1)
                RightAssociative -> (fixity + 1, fixity)
                NotAssociative   -> (fixity + 1, fixity + 1)
        in showPrettyFieldThunkS qualifyNames thunk lprec l
         . showString (" " ++ qualify name ++ " ")
         . showPrettyFieldThunkS qualifyNames thunk rprec r
    CustomD fixity list ->
      showParen (prec > fixity) $
        foldr (.) id $ flip fmap list $
          extractEither
          . bimap (showString . qualifyEither)
                  (\(f, pf) -> showPrettyFieldThunkS qualifyNames thunk f pf)
  where
    qualify (m, _, n) =
      if qualifyNames then (m ++ "." ++ n) else n
    qualifyEither (Left s) = s
    qualifyEither (Right (m, n)) =
      if qualifyNames then (m ++ "." ++ n) else n
    extractEither (Left x)  = x
    extractEither (Right x) = x

-- This precedence-aware pretty-printing algorithm is adapted from a solution
-- given by Brian Huffman on StackOverflow:
-- https://stackoverflow.com/questions/27471937/43639618#43639618

foldMapCompose :: (a -> (b -> b)) -> [a] -> (b -> b)
foldMapCompose f = appEndo . foldMap (Endo . f)


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

gProjectD :: GObserve a
          => (forall x. Observe x => x -> f x)
          -> a -> Demand a f
gProjectD p !(from -> sop) =
  GD (unSOP (hcliftA (Proxy :: Proxy Observe) (p . unI) sop))

gEmbedD :: GObserve a
        => (forall x. Observe x => f x -> x)
        -> Demand a f -> a
gEmbedD e !(GD d) =
  to (hcliftA (Proxy :: Proxy Observe) (I . e) (SOP d))

gMatchD :: forall a f g result. GObserve a
        => Demand a f -> Demand a g
        -> (forall xs. All Observe xs
              => Flattened (Demand a) f xs
              -> Maybe (Flattened (Demand a) g xs)
              -> result)
        -> result
gMatchD (GD df) (GD dg) cont =
  go @(Code a) df (Just dg) $ \flatF mflatG ->
    cont (flatGD flatF) (flatGD <$> mflatG)
  where
    go :: forall xss r.
      (All SListI xss, All2 Observe xss)
       => NS (NP f) xss
       -> Maybe (NS (NP g) xss)
       -> (forall xs. All Observe xs
             => Flattened (Flip SOP xss) f xs
             -> Maybe (Flattened (Flip SOP xss) g xs)
             -> r)
       -> r
    go (Z (fieldsF :: _ xs)) (Just (Z fieldsG)) k =
      k @xs (flatZ fieldsF)  (Just (flatZ fieldsG))
    go (Z (fieldsF :: _ xs)) _ k =   -- Nothing | Just (S _)
      k @xs (flatZ fieldsF)  Nothing
    go (S moreF) Nothing k =
      go moreF Nothing $ \(flatF :: _ xs) _ ->
        k @xs (flatS flatF) Nothing
    go (S moreF) (Just (Z _)) k =
      go moreF Nothing $ \(flatF :: _ xs) _ ->
        k @xs (flatS flatF) Nothing
    go (S moreF) (Just (S moreG)) k =
      go moreF (Just moreG) $ \(flatF :: _ xs) mflatG ->
        k @xs (flatS flatF) (flatS <$> mflatG)

    flatZ
      :: forall h xs xss. NP h xs -> Flattened (Flip SOP (xs : xss)) h xs
    flatZ = Flattened (Flip . SOP . Z)

    flatS
      :: forall h xs xs' xss.
      Flattened (Flip SOP xss) h xs
      -> Flattened (Flip SOP (xs' : xss)) h xs
    flatS (Flattened un fields) =
      Flattened (Flip . SOP . S . coerce . un) fields

    flatGD :: forall t h xs.
      Flattened (Flip SOP (Code t)) h xs -> Flattened (GDemand t) h xs
    flatGD (Flattened un fields) =
      Flattened (GD . coerce . un) fields

unFlip :: Flip f a b -> f b a
unFlip (Flip fba) = fba

gPrettyD :: forall a x. (HasDatatypeInfo a, GObserve a)
         => Demand a (K x) -> PrettyD x
gPrettyD (GD demand) =
  case info of
    ADT m d cs ->
      prettyC m d demand cs
    Newtype m d c ->
      prettyC m d demand (c :* Nil)
  where
    info = datatypeInfo (Proxy :: Proxy a)

    prettyC :: forall as. ModuleName -> DatatypeName
            -> NS (NP (K x)) as
            -> NP ConstructorInfo as
            -> PrettyD x
    prettyC m d subDemand constructors =
      case (subDemand, constructors) of
        (Z demandFields, c :* _) ->
          case c of
            Constructor name ->
              ConstructorD (m, d, name) $
                hcollapse demandFields
            Infix name associativity fixity ->
              case demandFields of
                (K a :* K b :* Nil) ->
                  InfixD (m, d, name) associativity fixity a b
            Record name fieldsInfo ->
              RecordD (m, d, name) $
                zip ( hcollapse
                    . hliftA (\(FieldInfo f) -> K (m, d, f))
                    $ fieldsInfo )
                    (hcollapse demandFields)
        (S another, _ :* different) ->
          prettyC m d another different

--------------------------------------
-- Deriving instances for things... --
--------------------------------------

deriving instance GHC.Generic (Field f a)
deriving instance (Eq     (f (Demand a (Field f)))) => Eq     (Field f a)
deriving instance (Ord    (f (Demand a (Field f)))) => Ord    (Field f a)
-- deriving instance (Show   (f (Demand a (Field f)))) => Show   (Field f a)
deriving newtype instance (NFData (f (Demand a (Field f)))) => NFData (Field f a)

instance Observe a => Show (Field Thunk a) where
  showsPrec d field =
    showParen (d > 10) $
      showPrettyFieldThunkS False "_" d (prettyField field)

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
deriving newtype instance ( SListI (Code a)
                  , All (Compose NFData (NP f)) (Code a)
                  ) => NFData (GDemand a f)
