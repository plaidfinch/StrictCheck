{-# LANGUAGE InstanceSigs #-}
{-# language PartialTypeSignatures #-}
{-# OPTIONS_GHC -fno-warn-partial-type-signatures #-}
{-| This module defines the 'Shaped' typeclass, which is used to reify
    substructures (prefixes) of values, and to generically observe their
    evaluation.

    If the functions you care about operate over datatypes which are all
    either 1) instances of 'Shaped' or 2) instances of GHC's 'GHC.Generic',
    testing these functions does not require you to work directly with the
    'Shaped' typeclass.

    To define new instances of 'Shaped' for types which implement 'GHC.Generic',
    an empty instance will suffice, as all the methods of 'Shaped' can be filled
    in by generic implementations. For example:

    > import GHC.Generics as GHC
    > import Generics.SOP as SOP
    >
    > data D = C deriving (GHC.Generic)
    >
    > instance SOP.Generic D
    > instance SOP.HasDatatypeInfo D
    >
    > instance Shaped D

    Using the @DeriveAnyClass@ extension, this can be shortened to one line:

    > data D = C deriving (GHC.Generic, SOP.Generic, SOP.HasDatatypeInfo, Shaped)

    Manual instances of 'Shaped' are necessary for types which do not or cannot
    implement GHC's @Generic@ typeclass, such as existential types, abstract
    types, and GADTs.
-}
module Test.StrictCheck.Shaped
  ( Shaped(..)
  -- * Fixed-points of 'Shape's
  , type (%)(..)
  , unwrap
  -- * Folds and unfolds over fixed-points of 'Shape's
  , interleave
  , (%)
  , fuse
  , translate
  , intrafold
  , extrafold
  , separate
  , module Data.Functor.Product
  , reshape
  -- * Rendering 'Shaped' things as structured text
  , Rendered(..)
  , RenderLevel(..)
  , renderfold
  -- * Generic implementation of the methods of 'Shaped'
  , GShaped
  , GShape(..)
  , gProject
  , gEmbed
  , gMatch
  , gRender
  ) where

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
  -- | The @Shape@ of an @a@ is a type isomorphic to the outermost level of
  -- structure in an @a@, parameterized by the functor @f@, which is wrapped
  -- around any fields (of any type) in the original @a@.
  --
  -- For instance, the @Shape@ of @Either a b@ might be:
  --
  -- > data EitherShape a b f
  -- >   = LeftShape  (f a)
  -- >   | RightShape (f b)
  -- >
  -- > instance Shaped (Either a b) where
  -- >   type Shape (Either a b) = EitherShape a b
  -- >   ...
  --
  -- The shape of a primitive type should be isomorphic to the primitive type,
  -- with the functor parameter left unused.
  type Shape a :: (* -> *) -> *
  type Shape a = GShape a

  -- | Given a function to expand any @Shaped@ @x@ into an @f x@, expand an @a@
  -- into a @Shape a f@
  --
  -- That is: convert the top-most level of structure in the given @a@ into a
  -- @Shape@, calling the provided function on each field in the @a@ to produce
  -- the @f x@ necessary to fill that hole in the produced @Shape a f@.
  --
  -- Inverse to 'embed'.
  project :: (forall x. Shaped x => x -> f x) -> a -> Shape a f

  default project
    :: GShaped a
    => (forall x. Shaped x => x -> f x)
    -> a
    -> Shape a f
  project = gProject

  -- | Given a function to collapse any @f x@ into a @Shaped@ @x@, collapse a
  -- @Shape a f@ into merely an @a@
  --
  -- That is: eliminate the top-most @Shape@ by calling the provided function on
  -- each field in that @Shape a f@, and using the results to fill in the pieces
  -- necessary to build an @a@.
  --
  -- Inverse to 'project'.
  embed :: (forall x. Shaped x => f x -> x) -> Shape a f -> a

  default embed
    :: GShaped a
    => (forall x. Shaped x => f x -> x)
    -> Shape a f
    -> a
  embed = gEmbed

  -- | Given two @Shape@s of the same type @a@ but parameterized by potentially
  -- different functors @f@ and @g@, pattern-match on them to expose a uniform
  -- view on their fields (a 'Flattened' @(Shape a)@) to a continuation which
  -- may operate on those fields to produce some result
  --
  -- If the two supplied @Shape@s do not structurally match, only the fields of
  -- the first are given to the continuation. If they do match, the fields of
  -- the second are also given, along with type-level proof that the types of
  -- the two sets of fields align.
  --
  -- This very general operation subsumes equality testing, mapping, zipping,
  -- shrinking, and many other structural operations over @Shaped@ things.
  --
  -- It is somewhat difficult to manually write instances for this method, but
  -- consulting its generic implementation 'gMatch' may prove helpful.
  --
  -- See "Test.StrictCheck.Shaped.Flattened" for more information.
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

  -- | Convert a @Shape a@ whose fields are some unknown constant type into a
  -- 'RenderLevel' filled with that type
  --
  -- This is a specialized pretty-printing mechanism which allows for displaying
  -- counterexamples in a structured format. See the documentation for
  -- 'RenderLevel'.
  render :: Shape a (K x) -> RenderLevel x

  default render :: (GShaped a, HasDatatypeInfo a)
          => Shape a (K x) -> RenderLevel x
  render = gRender


-------------------------------------
-- Manipulating interleaved Shapes --
-------------------------------------

-- | A value of type @f % a@ has the same structure as an @a@, but with the
-- structure of the functor @f@ interleaved at every field (including ones of
-- types other than @a@). Read this type aloud as "a interleaved with f's".
newtype (f :: * -> *) % (a :: *) :: * where
  Wrap :: f (Shape a ((%) f)) -> f % a

-- | Look inside a single level of an interleaved @f % a@. Inverse to the 'Wrap'
-- constructor.
unwrap :: f % a -> f (Shape a ((%) f))
unwrap (Wrap fs) = fs

-- | Map a function across all the fields in a 'Shape'
--
-- This function may change the functor over which the @Shape@ is parameterized.
-- It can assume recursively that all the fields in the @Shape@ are themselves
-- instances of @Shaped@ (which they should be!). This means that you can nest
-- calls to @translate@ recursively.
translate :: forall a f g. Shaped a
          => (forall x. Shaped x => f x -> g x)
          -> Shape a f -> Shape a g
translate t d = match @a d d $ \flat _ ->
  unflatten $ mapFlattened @Shaped t flat

-- | The equivalent of a fold (catamorphism) over recursively 'Shaped' values
--
-- Given a function which folds an @f@ containing some @Shape x g@ into a @g x@,
-- recursively fold any interleaved @f % a@ into a @g a@.
intrafold :: forall a f g. (Functor f, Shaped a)
          => (forall x. Shaped x => f (Shape x g) -> g x)
          -> f % a -> g a
intrafold alg = alg . fmap (translate @a (intrafold alg)) . unwrap

-- | The equivalent of an unfold (anamorphism) over recursively 'Shaped' values
--
-- Given a function which unfolds an @f x@ into a @g@ containing some @Shape x
-- f@, corecursively unfold any @f a@ into an interleaved @g % a@.
extrafold :: forall a f g. (Functor g, Shaped a)
          => (forall x. Shaped x => f x -> g (Shape x f))
          -> f a -> g % a
extrafold coalg = Wrap . fmap (translate @a (extrafold coalg)) . coalg

-- TODO: mapM, foldM, unfoldM, ...

-- | Fuse the interleaved @f@-structure out of a recursively interleaved @f %
-- a@, given some way of fusing a single level @f x -> x@.
--
-- This is a special case of 'intrafold'.
fuse :: forall a f. (Functor f, Shaped a)
     => (forall x. f x -> x)
     -> f % a -> a
fuse e = e . intrafold (fmap (embed e))

-- | Interleave an @f@-structure at every recursive level of some @a@, given
-- some way of generating a single level of structure @x -> f x@.
--
-- This is a special case of 'extrafold'.
interleave :: forall a f. (Functor f, Shaped a)
           => (forall x. x -> f x)
           -> a -> f % a
interleave p = extrafold (fmap (project p)) . p

-- | An infix synonym for 'interleave'
(%) :: forall a f. (Functor f, Shaped a)
    => (forall x. x -> f x)
    -> a -> f % a
(%) = interleave

-- | A higher-kinded @unzipWith@, operating over interleaved structures
--
-- Given a function splitting some @f x@ into a functor-product @Product g h x@,
-- recursively split an interleaved @f % a@ into two interleaved structures:
-- one built of @g@-shapes and one of @h@-shapes.
--
-- Note that @Product ((%) g) ((%) h) a@ is isomorphic to @(g % a, h % a)@; to
-- get the latter, pattern-match on the 'Pair' constructor of 'Product'.
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

-- | TODO: document this strange function
reshape :: forall b a f g. (Shaped a, Shaped b, Functor f)
        => (f (Shape b ((%) g)) -> g (Shape b ((%) g)))
        -> (forall x. Shaped x => f % x -> g % x)
        -> f % a -> g % a
reshape homo hetero d =
  case eqT @a @b of
    Nothing   -> hetero d
    Just Refl ->
      Wrap
      $ homo . fmap (translate @a (reshape @b homo hetero))
      $ unwrap d



----------------------------------
-- Rendering shapes for display --
----------------------------------

-- | Convert an @f % a@ into a structured pretty-printing representation,
-- suitable for further display/processing
renderfold :: forall a f. (Shaped a, Functor f)
       => f % a -> Rendered f
renderfold = unK . intrafold oneLevel
  where
    oneLevel :: forall x. Shaped x
             => f (Shape x (K (Rendered f)))
             -> K (Rendered f) x
    oneLevel = K . RWrap . fmap (render @x)

-- | A @QName@ is a qualified name
--
-- Note:
-- > type ModuleName   = String
-- > type DatatypeName = String
type QName = (ModuleName, DatatypeName, String)

data RenderLevel x
  = ConstructorD QName [x]
  -- ^ A prefix constructor, and a list of its fields
  | InfixD QName Associativity Fixity x x
  -- ^ An infix constructor, its associativity and fixity, and its two fields
  | RecordD QName [(QName, x)]
  -- ^ A record constructor, and a list of its field names paired with fields
  | CustomD Fixity
    [Either (Either String (ModuleName, String)) (Fixity, x)]
  -- ^ A custom pretty-printing representation (i.e. for abstract types), which
  -- records a fixity and a list of tokens of three varieties: 1) raw strings,
  -- 2) qualified strings (from some module), or 3) actual fields, annotated
  -- with their fixity
  deriving (Eq, Ord, Show, Functor)

-- | @Rendered f@ is the fixed-point of @f@ composed with 'RenderLevel': it
-- alternates between @f@ shapes and @RenderLevel@s. Usually, @f@ will be the
-- identity functor 'I', but not always.
data Rendered f =
  RWrap (f (RenderLevel (Rendered f)))

deriving instance Eq   (f (RenderLevel (Rendered f))) => Eq   (Rendered f)
deriving instance Ord  (f (RenderLevel (Rendered f))) => Ord  (Rendered f)
deriving instance Show (f (RenderLevel (Rendered f))) => Show (Rendered f)


---------------------------------------------------
-- Generic implementation of the Shaped methods --
---------------------------------------------------

newtype GShape a f =
  GS (NS (NP f) (Code a))

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
  GS (unSOP (hcliftA (Proxy :: Proxy Shaped) (p . unI) sop))

gEmbed :: GShaped a
       => (forall x. Shaped x => f x -> x)
       -> Shape a f -> a
gEmbed e !(GS d) =
  to (hcliftA (Proxy :: Proxy Shaped) (I . e) (SOP d))

gMatch :: forall a f g result. GShaped a
       => Shape a f -> Shape a g
       -> (forall xs. All Shaped xs
             => Flattened (Shape a) f xs
             -> Maybe (Flattened (Shape a) g xs)
             -> result)
       -> result
gMatch !(GS df) !(GS dg) cont =
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
      Flattened (GS . coerce . un) fields

gRender :: forall a x. (HasDatatypeInfo a, GShaped a)
         => Shape a (K x) -> RenderLevel x
gRender (GS demand) =
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

instance Num (f (Shape a ((%) f))) => Num (f % a) where
  (+)         = onWrap2 (+)
  (-)         = onWrap2 (-)
  (*)         = onWrap2 (*)
  abs         = onWrap abs
  signum      = onWrap signum
  fromInteger = Wrap . fromInteger

onWrap :: (f (Shape a ((%) f)) -> f (Shape b ((%) f)))
       -> f % a -> f % b
onWrap f (Wrap a) = Wrap (f a)

onWrap2 :: (f (Shape a ((%) f)) -> f (Shape b ((%) f)) -> f (Shape c ((%) f)))
        -> f % a -> f % b -> f % c
onWrap2 f (Wrap a) (Wrap b) = Wrap (f a b)

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
