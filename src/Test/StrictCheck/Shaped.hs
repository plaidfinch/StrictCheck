{-# LANGUAGE InstanceSigs #-}
{-# language PartialTypeSignatures #-}
{-# OPTIONS_GHC -fno-warn-partial-type-signatures #-}
module Test.StrictCheck.Shaped where

import Data.Typeable
import Data.Functor.Product
import Data.Bifunctor
import Data.Bifunctor.Flip
import Data.Coerce
import Control.DeepSeq

import Generics.SOP hiding ( Shape )
import qualified GHC.Generics as GHC

import Test.StrictCheck.Shaped.Flattened

-- TODO: provide instances for all of Base

class Typeable a => Shaped (a :: *) where
  type Shape a :: (* -> *) -> *
  type Shape a = GShape a

  project :: (forall x. Shaped x => x -> f x) -> a -> Shape a f
  default project :: GShaped a
          => (forall x. Shaped x => x -> f x) -> a -> Shape a f
  project = gProject

  embed :: (forall x. Shaped x => f x -> x) -> Shape a f -> a
  default embed :: GShaped a
        => (forall x. Shaped x => f x -> x) -> Shape a f -> a
  embed = gEmbed

  match :: Shape a f -> Shape a g
        -> (forall xs. All Shaped xs
              => Flattened (Shape a) f xs
              -> Maybe (Flattened (Shape a) g xs)
              -> result)
        -> result
  default match :: GShaped a
        => Shape a f -> Shape a g
        -> (forall xs. All Shaped xs
              => Flattened (Shape a) f xs
              -> Maybe (Flattened (Shape a) g xs)
              -> result)
        -> result
  match = gMatch

  render :: Shape a (K x) -> RenderLevel x
  default render :: (GShaped a, HasDatatypeInfo a)
          => Shape a (K x) -> RenderLevel x
  render = gRender


-- TODO: Derive single-value match, and a default-if-not-same match

-------------------------------------
-- Manipulating interleaved Shapes --
-------------------------------------

newtype (f :: * -> *) % (a :: *) :: * where
  Wrap :: f (Shape a ((%) f)) -> f % a

unwrap :: f % a -> f (Shape a ((%) f))
unwrap (Wrap fs) = fs

translate :: forall a f g. Shaped a
          => (forall x. Shaped x => f x -> g x)
          -> Shape a f -> Shape a g
translate t d = match @a d d $ \flat _ ->
  unflatten $ mapFlattened @Shaped t flat

intrafold :: forall a f g. (Functor f, Shaped a)
          => (forall x. Shaped x => f (Shape x g) -> g x)
          -> f % a -> g a
intrafold alg = alg . fmap (translate @a (intrafold alg)) . unwrap

extrafold :: forall a f g. (Functor g, Shaped a)
          => (forall x. Shaped x => f x -> g (Shape x f))
          -> f a -> g % a
extrafold coalg = Wrap . fmap (translate @a (extrafold coalg)) . coalg

-- TODO: mapM, foldM, unfoldM, ...

(%) :: forall a f. (Functor f, Shaped a)
    => (forall x. x -> f x)
    -> a -> f % a
(%) = interleave

interleave :: forall a f. (Functor f, Shaped a)
           => (forall x. x -> f x)
           -> a -> f % a
interleave p = extrafold (fmap (project p)) . p

fuse :: forall a f. (Functor f, Shaped a)
     => (forall x. f x -> x)
     -> f % a -> a
fuse e = e . intrafold (fmap (embed e))

separate :: forall a f g h.
         (Shaped a, Functor f, Functor g, Functor h)
         => (forall x. f x -> Product g h x)
         -> f % a -> Product ((%) g) ((%) h) a
separate split =
  intrafold (crunch . split)
  where
    crunch :: forall x. Shaped x
           => Product g h (Shape x (Product ((%) g) ((%) h)))
           -> Product ((%) g) ((%) h) x
    crunch =
      uncurry Pair
      . bimap (Wrap . fmap (translate @x (\(Pair l _) -> l)))
              (Wrap . fmap (translate @x (\(Pair _ r) -> r)))
      . (\(Pair l r) -> (l, r))


----------------------------------
-- Rendering shapes for display --
----------------------------------

renderfold :: forall a f. (Shaped a, Functor f)
       => f % a -> Rendered f
renderfold = unK . intrafold oneLevel
  where
    oneLevel :: forall x. Shaped x
             => f (Shape x (K (Rendered f)))
             -> K (Rendered f) x
    oneLevel = K . RWrap . fmap (render @x)

data RenderLevel x = ConstructorD QName [x]
                   | InfixD QName Associativity Fixity x x
                   | RecordD QName [(QName, x)]
                   | CustomD Fixity
                      [Either (Either String (ModuleName, String)) (Fixity, x)]
                   deriving (Eq, Ord, Show, Functor)

data Rendered f =
  RWrap (f (RenderLevel (Rendered f)))

deriving instance Eq   (f (RenderLevel (Rendered f))) => Eq   (Rendered f)
deriving instance Ord  (f (RenderLevel (Rendered f))) => Ord  (Rendered f)
deriving instance Show (f (RenderLevel (Rendered f))) => Show (Rendered f)

type QName = (ModuleName, DatatypeName, String)



---------------------------------------------------
-- Generic implementation of the Shaped methods --
---------------------------------------------------

newtype GShape a f =
  GD (NS (NP f) (Code a))

type GShaped a =
  ( Generic a
  , Shape a ~ GShape a
  , All2 Shaped (Code a)
  , SListI (Code a)
  , All SListI (Code a) )

gProject :: GShaped a
         => (forall x. Shaped x => x -> f x)
         -> a -> Shape a f
gProject p !(from -> sop) =
  GD (unSOP (hcliftA (Proxy :: Proxy Shaped) (p . unI) sop))

gEmbed :: GShaped a
       => (forall x. Shaped x => f x -> x)
       -> Shape a f -> a
gEmbed e !(GD d) =
  to (hcliftA (Proxy :: Proxy Shaped) (I . e) (SOP d))

gMatch :: forall a f g result. GShaped a
       => Shape a f -> Shape a g
       -> (forall xs. All Shaped xs
             => Flattened (Shape a) f xs
             -> Maybe (Flattened (Shape a) g xs)
             -> result)
       -> result
gMatch !(GD df) !(GD dg) cont =
  go @(Code a) df (Just dg) $ \flatF mflatG ->
    cont (flatGD flatF) (flatGD <$> mflatG)
  where
    go :: forall xss r.
      (All SListI xss, All2 Shaped xss)
       => NS (NP f) xss
       -> Maybe (NS (NP g) xss)
       -> (forall xs. All Shaped xs
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
      Flattened (Flip SOP (Code t)) h xs -> Flattened (GShape t) h xs
    flatGD (Flattened un fields) =
      Flattened (GD . coerce . un) fields

gRender :: forall a x. (HasDatatypeInfo a, GShaped a)
         => Shape a (K x) -> RenderLevel x
gRender (GD demand) =
  case info of
    ADT m d cs ->
      renderC m d demand cs
    Newtype m d c ->
      renderC m d demand (c :* Nil)
  where
    info = datatypeInfo (Proxy :: Proxy a)

    renderC :: forall as. ModuleName -> DatatypeName
            -> NS (NP (K x)) as
            -> NP ConstructorInfo as
            -> RenderLevel x
    renderC m d subShape constructors =
      case (subShape, constructors) of
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
          renderC m d another different


--------------------------------------
-- Deriving instances for things... --
--------------------------------------

deriving instance GHC.Generic (f % a)
deriving stock   instance (Eq     (f (Shape a ((%) f)))) => Eq     (f % a)
deriving stock   instance (Ord    (f (Shape a ((%) f)))) => Ord    (f % a)
deriving stock   instance (Show   (f (Shape a ((%) f)))) => Show   (f % a)
deriving newtype instance (NFData (f (Shape a ((%) f)))) => NFData (f % a)

deriving instance GHC.Generic (GShape a f)
deriving instance ( SListI (Code a)
                  , All (Compose Eq (NP f)) (Code a)
                  ) => Eq (GShape a f)
deriving instance ( SListI (Code a)
                  , All (Compose Eq (NP f)) (Code a)
                  , All (Compose Ord (NP f)) (Code a)
                  ) => Ord (GShape a f)
deriving instance ( SListI (Code a)
                  , All (Compose Show (NP f)) (Code a)
                  ) => Show (GShape a f)
deriving newtype instance ( SListI (Code a)
                  , All (Compose NFData (NP f)) (Code a)
                  ) => NFData (GShape a f)
