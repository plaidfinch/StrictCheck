{-# language InstanceSigs, DerivingStrategies #-}
{-# language PartialTypeSignatures #-}
{-# OPTIONS_GHC -fno-warn-partial-type-signatures #-}
{-| This module defines the 'Shaped' typeclass, which is used to generically
    manipulate values as fixed-points of higher-order functors in order to
    analyze their structure, e.g. while observing evaluation.

    If you just care about testing the strictness of functions over datatypes
    which are already instances of @Shaped@, you don't need to use this module.

    __Important note:__ To define new instances of 'Shaped' for types which
    implement 'GHC.Generic', __an empty instance will suffice__, as all the
    methods of 'Shaped' can be filled in by generic implementations. For
    example:

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

    This module is heavily based upon the approach in "Data.Functor.Foldable",
    which in turn is modeled after the paper "Functional Programming with
    Bananas, Lenses, Envelopes and Barbed Wire" (1991) by Erik Meijer, Maarten
    Fokkinga and Ross Paterson. If you don't yet understand recursion schemes
    and want to understand this module, it's probably a good idea to familiarize
    yourself with "Data.Functor.Foldable" before diving into this higher-order
    generalization.
-}
module Test.StrictCheck.Shaped
  ( Shaped(..)
  , module Test.StrictCheck.Shaped.Flattened
  -- * Fixed-points of 'Shape's
  , type (%)(..)
  -- * Folds and unfolds over fixed-points of @Shape@s
  , unwrap
  , interleave
  , (%)
  , fuse
  , translate
  , fold
  , unfold
  , unzipWith
  -- , reshape
  -- * Rendering 'Shaped' things as structured text
  , QName
  , Rendered(..)
  , RenderLevel(..)
  , renderfold
  -- * Tools for manually writing instances of 'Shaped'
  -- ** Implementing 'Shaped' for primitive types
  , Prim(..), unPrim
  , projectPrim
  , embedPrim
  , matchPrim
  , flatPrim
  , renderPrim
  , renderConstant
  -- ** Implementing 'Shaped' for container types
  , Containing(..)
  , projectContainer
  , embedContainer
  -- * Generic implementation of the methods of 'Shaped'
  , GShaped
  , GShape(..)
  , gProject
  , gEmbed
  , gMatch
  , gRender
  ) where

import Type.Reflection
import Data.Functor.Product
import Data.Bifunctor
import Data.Bifunctor.Flip
import Data.Coerce

import Generics.SOP hiding ( Shape )

import Data.Complex
-- import Data.List.NonEmpty (NonEmpty(..))

import Test.StrictCheck.Shaped.Flattened

-- TODO: provide instances for all of Base

-- | When a type @a@ is @Shaped@, we know how to convert it into a
-- representation parameterized by an arbitrary functor @f@, so that @Shape a f@
-- (the "shape of @a@ parameterized by @f@") is structurally identical to the
-- topmost structure of @a@, but with @f@ wrapped around any subfields of @a@.
--
-- Note that this is /not/ a recursive representation! The functor @f@ in
-- question wraps the original type of the field and /not/ a @Shape@ of that
-- field.
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
class Typeable a => Shaped (a :: *) where
  -- | The @Shape@ of an @a@ is a type isomorphic to the outermost level of
  -- structure in an @a@, parameterized by the functor @f@, which is wrapped
  -- around any fields (of any type) in the original @a@.
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



-- * Fixed-points of 'Shape's

-- | A value of type @f % a@ has the same structure as an @a@, but with the
-- structure of the functor @f@ interleaved at every field (including ones of
-- types other than @a@). Read this type aloud as "a interleaved with f's".
newtype (f :: * -> *) % (a :: *) :: * where
  Wrap :: f (Shape a ((%) f)) -> f % a

-- | Look inside a single level of an interleaved @f % a@. Inverse to the 'Wrap'
-- constructor.
unwrap :: f % a -> f (Shape a ((%) f))
unwrap (Wrap fs) = fs



-- * Folds and unfolds over fixed-points of @Shape@s

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
fold :: forall a f g. (Functor f, Shaped a)
     => (forall x. Shaped x => f (Shape x g) -> g x)
     -> f % a -> g a
fold alg = alg . fmap (translate @a (fold alg)) . unwrap

-- | The equivalent of an unfold (anamorphism) over recursively 'Shaped' values
--
-- Given a function which unfolds an @f x@ into a @g@ containing some @Shape x
-- f@, corecursively unfold any @f a@ into an interleaved @g % a@.
unfold :: forall a f g. (Functor g, Shaped a)
       => (forall x. Shaped x => f x -> g (Shape x f))
       -> f a -> g % a
unfold coalg = Wrap . fmap (translate @a (unfold coalg)) . coalg

-- TODO: mapM, foldM, unfoldM, ...

-- | Fuse the interleaved @f@-structure out of a recursively interleaved @f %
-- a@, given some way of fusing a single level @f x -> x@.
--
-- This is a special case of 'fold'.
fuse
  :: (Functor f, Shaped a)
  => (forall x. f x -> x)
  -> (f % a -> a)
fuse e = e . fold (fmap (embed e))

-- | Interleave an @f@-structure at every recursive level of some @a@, given
-- some way of generating a single level of structure @x -> f x@.
--
-- This is a special case of 'unfold'.
interleave
  :: (Functor f, Shaped a)
  => (forall x. x -> f x)
  -> (a -> f % a)
interleave p = unfold (fmap (project p)) . p

-- | An infix synonym for 'interleave'
(%) :: forall a f. (Functor f, Shaped a)
    => (forall x. x -> f x)
    -> a -> f % a
(%) = interleave

-- | A higher-kinded @unzipWith@, operating over interleaved structures
--
-- Given a function splitting some @f x@ into a @g x@ and a @h x@, unzip and
-- entire @f % a@ structure using this operation, yielding a @g % a@ and a
-- @h % a@.
unzipWith
  :: (All Functor [f, g, h], Shaped a)
  => (forall x. f x -> (g x, h x))
  -> (f % a -> (g % a, h % a))
unzipWith split =
  unPair . fold (crunch . pair . split)
  where
    crunch
      :: forall x g h.
      (Shaped x, Functor g, Functor h)
      => Product g h (Shape x (Product ((%) g) ((%) h)))
      -> Product ((%) g) ((%) h) x
    crunch =
      pair
      . bimap (Wrap . fmap (translate @x (fst . unPair)))
              (Wrap . fmap (translate @x (snd . unPair)))
      . unPair

    pair :: (l x, r x) -> Product l r x
    pair = uncurry Pair

    unPair :: Product l r x -> (l x, r x)
    unPair (Pair lx rx) = (lx, rx)

-- | TODO: document this strange function
{-
reshape :: forall b a f g. (Shaped a, Shaped b, Functor f)
        => (f (Shape b ((%) g)) -> g (Shape b ((%) g)))
        -> (forall x. Shaped x => f % x -> g % x)
        -> f % a -> g % a
reshape homo hetero d =
  case eqTypeRep (typeRep @a) (typeRep @b) of
    Nothing    -> hetero d
    Just HRefl ->
      Wrap
      $ homo . fmap (translate @a (reshape @b homo hetero))
      $ unwrap d
-}

----------------------------------
-- Rendering shapes for display --
----------------------------------

-- | Convert an @f % a@ into a structured pretty-printing representation,
-- suitable for further display/processing
renderfold
  :: forall a f. (Shaped a, Functor f)
  => f % a -> Rendered f
renderfold = unK . fold oneLevel
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

-- | @RenderLevel@ is a functor whose outer shape contains all the information
-- about how to pretty-format the outermost @Shape@ of some value. We use
-- parametricity to make it difficult to construct incorrect 'render' methods,
-- by asking the user merely to produce a single @RenderLevel@ and stitching
-- nested @RenderLevel@s into complete 'Rendered' trees.
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
data Rendered f
  = RWrap (f (RenderLevel (Rendered f)))


----------------------------------------------------
-- Tools for manually writing instances of Shaped --
----------------------------------------------------

-- | The @Shape@ of a spine-strict container (i.e. a @Map@ or @Set@) is the same
-- as a container of demands on its elements. However, this does not have the
-- right /kind/ to be used as a @Shape@.
--
-- The @Containing@ newtype solves this problem. By defining the @Shape@ of some
-- container @(C a)@ to be @(C `Containing` a)@, you can use the methods
-- @projectContainer@ and @embedContainer@ to implement @project@ and @embed@
-- for your container type (although you will still need to manually define
-- @match@ and @render@).
newtype Containing h a f
  = Container (h (f a))
  deriving (Eq, Ord, Show)

-- | Generic implementation of @project@ for any container type whose @Shape@
-- is represented as a @Containing@ newtype
projectContainer :: (Functor c, Shaped a)
  => (forall x. Shaped x => x -> f x)
  -> c a -> Containing c a f
projectContainer p x = Container (fmap p x)

-- | Generic implementation of @embed@ for any container type whose @Shape@
-- is represented as a @Containing@ newtype
embedContainer :: (Functor c, Shaped a)
  => (forall x. Shaped x => f x -> x)
  -> Containing c a f -> c a
embedContainer e (Container x) = fmap e x


-- TODO: helper functions for matching and prettying containers

-- | The @Shape@ of a primitive type should be equivalent to the type itself.
-- However, this does not have the right /kind/ to be used as a @Shape@.
--
-- The @Prim@ newtype solves this problem. By defining the @Shape@ of some
-- primitive type @p@ to be @Prim p@, you can use the methods @projectPrim@,
-- @embedPrim@, @matchPrim@, and @prettyPrim@ to completely fill in the
-- definition of the @Shaped@ class for a primitive type.
--
-- __Note:__ It is only appropriate to use this @Shape@ representation when a
-- type really is primitive, in that it contains no interesting substructure.
-- If you use the @Prim@ representation inappropriately, StrictCheck will not be
-- able to inspect the richer structure of the type in question.
newtype Prim (x :: *) (f :: * -> *)
  = Prim x
  deriving (Eq, Ord, Show)
  deriving newtype (Num)

-- | Get the wrapped @x@ out of a @Prim x f@ (inverse to the @Prim@ constructor)
unPrim :: Prim x f -> x
unPrim (Prim x) = x

-- | Generic implementation of @project@ for any primitive type whose @Shape@ is
-- is represented as a @Prim@ newtype
projectPrim :: (forall x. Shaped x => x -> f x) -> a -> Prim a f
projectPrim _ = Prim

-- | Generic implementation of @embed@ for any primitive type whose @Shape@ is
-- is represented as a @Prim@ newtype
embedPrim :: (forall x. Shaped x => f x -> x) -> Prim a f -> a
embedPrim _ = unPrim

-- | Generic implementation of @match@ for any primitive type whose @Shape@ is
-- is represented as a @Prim@ newtype with an underlying @Eq@ instance
matchPrim :: Eq a => Prim a f -> Prim a g
           -> (forall xs. All Shaped xs
                => Flattened (Prim a) f xs
                -> Maybe (Flattened (Prim a) g xs)
                -> result)
           -> result
matchPrim (Prim a) (Prim b) k =
  k (flatPrim a)
     (if a == b then (Just (flatPrim b)) else Nothing)

-- | Helper for writing @match@ instances for primitive types which don't have
-- @Eq@ instance
--
-- This generates a @Flattened@ appropriate for using in the implementation of
-- @match@. For more documentation on how to use this, see the documentation of
-- 'match'.
flatPrim :: a -> Flattened (Prim a) g '[]
flatPrim x = Flattened (const (Prim x)) Nil

-- | Generic implementation of @render@ for any primitive type whose @Shape@ is
-- is represented as a @Prim@ newtype
renderPrim :: Show a => Prim a (K x) -> RenderLevel x
renderPrim (Prim a) = renderConstant (show a)

-- | Given some @string@, generate a custom pretty-printing representation which
-- just shows the string
renderConstant :: String -> RenderLevel x
renderConstant s = CustomD 11 [Left (Left s)]

-- TODO: What about demands for abstract types with > 1 type of unbounded-count field?

{-
withFieldsContainer ::
  forall c a f result.
     (forall r h.
        c (h a) ->
        (forall x. Shaped x
           => [h x]
           -> (forall g. [g x] -> c (g a))
           -> r)
        -> r)
  -> Containing c a f
  -> (forall xs. All Shaped xs
        => NP f xs
        -> (forall g. NP g xs -> Containing c a g)
        -> result)
  -> result
withFieldsContainer viaContaining (Container c) cont =
  viaContaining c $
    \list un ->
       withNP @Shaped list (Container . un) cont

-- TODO: Make this work for any number of lists of fields, by carefully using
-- unsafeCoerce to deal with unknown list lengths

withFieldsViaList ::
  forall demand f result.
     (forall r h.
        demand h ->
        (forall x. Shaped x
           => [h x]
           -> (forall g. [g x] -> demand g)
           -> r)
        -> r)
  -> demand f
  -> (forall xs. All Shaped xs
        => NP f xs
        -> (forall g. NP g xs -> demand g)
        -> result)
  -> result
withFieldsViaList viaList demand cont =
  viaList demand $
    \list un ->
       withNP @Shaped list un cont

withNP :: forall c demand result f x. c x
       => [f x]
       -> (forall g. [g x] -> demand g)
       -> (forall xs. All c xs
             => NP f xs -> (forall g. NP g xs -> demand g) -> result)
       -> result
withNP list unList cont =
  withUnhomogenized @c list $ \np ->
    cont np (unList . homogenize)

withConcatenated :: NP (NP f) xss -> (forall xs. NP f xs -> r) -> r
withConcatenated pop cont =
  case pop of
    Nil         -> cont Nil
    (xs :* xss) -> withConcatenated xss (withPrepended xs cont)
  where
    withPrepended ::
      NP f ys -> (forall zs. NP f zs -> r)
              -> (forall zs. NP f zs -> r)
    withPrepended pre k rest =
      case pre of
        Nil        -> k rest
        (x :* xs)  -> withPrepended xs (k . (x :*)) rest

homogenize :: All ((~) a) as => NP f as -> [f a]
homogenize      Nil  = []
homogenize (a :* as) = a : homogenize as

withUnhomogenized :: forall c a f r.
  c a => [f a] -> (forall as. (All c as, All ((~) a) as) => NP f as -> r) -> r
withUnhomogenized      []  k = k Nil
withUnhomogenized (a : as) k =
  withUnhomogenized @c as $ \np -> k (a :* np)
-}


---------------------------------------------------
-- Generic implementation of the Shaped methods --
---------------------------------------------------

-- | The 'Shape' used for generic implementations of 'Shaped'
--
-- This wraps a sum-of-products representation from "Generics.SOP".
newtype GShape a f
  = GS (NS (NP f) (Code a))

-- | The collection of constraints necessary for a type to be given a generic
-- implementation of the 'Shaped' methods
type GShaped a =
  ( Generic a
  , Shape a ~ GShape a
  , All2 Shaped (Code a)
  , SListI (Code a)
  , All SListI (Code a) )

-- | Generic 'project'
gProject :: GShaped a
         => (forall x. Shaped x => x -> f x)
         -> a -> Shape a f
gProject p !(from -> sop) =
  GS (unSOP (hcliftA (Proxy @Shaped) (p . unI) sop))

-- | Generic 'embed'
gEmbed :: GShaped a
       => (forall x. Shaped x => f x -> x)
       -> Shape a f -> a
gEmbed e !(GS d) =
  to (hcliftA (Proxy @Shaped) (I . e) (SOP d))

-- | Generic 'match'
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

-- | Generic 'render'
gRender :: forall a x. (HasDatatypeInfo a, GShaped a)
         => Shape a (K x) -> RenderLevel x
gRender (GS demand) =
  case info of
    ADT m d cs ->
      renderC m d demand cs
    Newtype m d c ->
      renderC m d demand (c :* Nil)
  where
    info = datatypeInfo (Proxy @a)

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


---------------
-- Instances --
---------------

instance Shaped ()
instance Shaped Bool
instance Shaped Ordering
instance Shaped a => Shaped (Maybe a)
instance (Shaped a, Shaped b) => Shaped (Either a b)
instance Shaped a => Shaped [a]

instance (Typeable a, Typeable b) => Shaped (a -> b) where
  type Shape (a -> b) = Prim (a -> b)
  project = projectPrim
  embed = embedPrim
  match (Prim f) (Prim g) k = k (flatPrim f) (Just $ flatPrim g)
  render _ = renderConstant ("<function> :: " ++ show (typeRep @(a -> b)))

instance Shaped Char where
  type Shape Char = Prim Char
  project = projectPrim
  embed   = embedPrim
  match   = matchPrim
  render  = renderPrim

instance Shaped Word where
  type Shape Word = Prim Word
  project = projectPrim
  embed   = embedPrim
  match   = matchPrim
  render  = renderPrim

instance Shaped Int where
  type Shape Int = Prim Int
  project = projectPrim
  embed   = embedPrim
  match   = matchPrim
  render  = renderPrim

instance Shaped Double where
  type Shape Double = Prim Double
  project = projectPrim
  embed   = embedPrim
  match   = matchPrim
  render  = renderPrim

instance Shaped Float where
  type Shape Float = Prim Float
  project = projectPrim
  embed   = embedPrim
  match   = matchPrim
  render  = renderPrim

instance Shaped Rational where
  type Shape Rational = Prim Rational
  project = projectPrim
  embed   = embedPrim
  match   = matchPrim
  render  = renderPrim

instance Shaped Integer where
  type Shape Integer = Prim Integer
  project = projectPrim
  embed   = embedPrim
  match   = matchPrim
  render  = renderPrim

instance (Typeable a, Eq a, Show a) => Shaped (Complex a) where
  type Shape (Complex a) = Prim (Complex a)
  project = projectPrim
  embed   = embedPrim
  match   = matchPrim
  render  = renderPrim

-- instance Generic (NonEmpty a)
-- instance HasDatatypeInfo (NonEmpty a)
-- instance Shaped a => Shaped (NonEmpty a) where

-- Tree
-- Map k
-- Seq
-- Set
-- IntMap
-- IntSet

instance (Shaped a, Shaped b) => Shaped (a, b)
instance (Shaped a, Shaped b, Shaped c) => Shaped (a, b, c)
instance (Shaped a, Shaped b, Shaped c, Shaped d) => Shaped (a, b, c, d)
instance ( Shaped a, Shaped b, Shaped c, Shaped d, Shaped e
         ) => Shaped
  (a, b, c, d, e)
instance ( Shaped a, Shaped b, Shaped c, Shaped d, Shaped e, Shaped f
         ) => Shaped
  (a, b, c, d, e, f)
instance ( Shaped a, Shaped b, Shaped c, Shaped d, Shaped e, Shaped f
         , Shaped g
         ) => Shaped
  (a, b, c, d, e, f, g)
-- instance ( Shaped a, Shaped b, Shaped c, Shaped d, Shaped e, Shaped f
--          , Shaped g, Shaped h
--          ) => Shaped
--   (a, b, c, d, e, f, g, h)
-- instance ( Shaped a, Shaped b, Shaped c, Shaped d, Shaped e, Shaped f
--          , Shaped g, Shaped h, Shaped i
--          ) => Shaped
--   (a, b, c, d, e, f, g, h, i)
-- instance ( Shaped a, Shaped b, Shaped c, Shaped d, Shaped e, Shaped f
--          , Shaped g, Shaped h, Shaped i, Shaped j
--          ) => Shaped
--   (a, b, c, d, e, f, g, h, i, j)
-- instance ( Shaped a, Shaped b, Shaped c, Shaped d, Shaped e, Shaped f
--          , Shaped g, Shaped h, Shaped i, Shaped j, Shaped k
--          ) => Shaped
--   (a, b, c, d, e, f, g, h, i, j, k)
-- instance ( Shaped a, Shaped b, Shaped c, Shaped d, Shaped e, Shaped f
--          , Shaped g, Shaped h, Shaped i, Shaped j, Shaped k, Shaped l
--          ) => Shaped
--   (a, b, c, d, e, f, g, h, i, j, k, l)
-- instance ( Shaped a, Shaped b, Shaped c, Shaped d, Shaped e, Shaped f
--          , Shaped g, Shaped h, Shaped i, Shaped j, Shaped k, Shaped l
--          , Shaped m
--          ) => Shaped
--   (a, b, c, d, e, f, g, h, i, j, k, l, m)
-- instance ( Shaped a, Shaped b, Shaped c, Shaped d, Shaped e, Shaped f
--          , Shaped g, Shaped h, Shaped i, Shaped j, Shaped k, Shaped l
--          , Shaped m, Shaped n
--          ) => Shaped
--   (a, b, c, d, e, f, g, h, i, j, k, l, m, n)
-- instance ( Shaped a, Shaped b, Shaped c, Shaped d, Shaped e, Shaped f
--          , Shaped g, Shaped h, Shaped i, Shaped j, Shaped k, Shaped l
--          , Shaped m, Shaped n, Shaped o
--          ) => Shaped
--   (a, b, c, d, e, f, g, h, i, j, k, l, m, n, o)
-- instance ( Shaped a, Shaped b, Shaped c, Shaped d, Shaped e, Shaped f
--          , Shaped g, Shaped h, Shaped i, Shaped j, Shaped k, Shaped l
--          , Shaped m, Shaped n, Shaped o, Shaped p
--          ) => Shaped
--   (a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p)
-- instance ( Shaped a, Shaped b, Shaped c, Shaped d, Shaped e, Shaped f
--          , Shaped g, Shaped h, Shaped i, Shaped j, Shaped k, Shaped l
--          , Shaped m, Shaped n, Shaped o, Shaped p, Shaped q
--          ) => Shaped
--   (a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q)
-- instance ( Shaped a, Shaped b, Shaped c, Shaped d, Shaped e, Shaped f
--          , Shaped g, Shaped h, Shaped i, Shaped j, Shaped k, Shaped l
--          , Shaped m, Shaped n, Shaped o, Shaped p, Shaped q, Shaped r
--          ) => Shaped
--   (a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r)
-- instance ( Shaped a, Shaped b, Shaped c, Shaped d, Shaped e, Shaped f
--          , Shaped g, Shaped h, Shaped i, Shaped j, Shaped k, Shaped l
--          , Shaped m, Shaped n, Shaped o, Shaped p, Shaped q, Shaped r
--          , Shaped s
--          ) => Shaped
--   (a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s)
-- instance ( Shaped a, Shaped b, Shaped c, Shaped d, Shaped e, Shaped f
--          , Shaped g, Shaped h, Shaped i, Shaped j, Shaped k, Shaped l
--          , Shaped m, Shaped n, Shaped o, Shaped p, Shaped q, Shaped r
--          , Shaped s, Shaped t
--          ) => Shaped
--   (a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t)
-- instance ( Shaped a, Shaped b, Shaped c, Shaped d, Shaped e, Shaped f
--          , Shaped g, Shaped h, Shaped i, Shaped j, Shaped k, Shaped l
--          , Shaped m, Shaped n, Shaped o, Shaped p, Shaped q, Shaped r
--          , Shaped s, Shaped t, Shaped u
--          ) => Shaped
--   (a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u)
-- instance ( Shaped a, Shaped b, Shaped c, Shaped d, Shaped e, Shaped f
--          , Shaped g, Shaped h, Shaped i, Shaped j, Shaped k, Shaped l
--          , Shaped m, Shaped n, Shaped o, Shaped p, Shaped q, Shaped r
--          , Shaped s, Shaped t, Shaped u, Shaped v
--          ) => Shaped
--   (a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v)
-- instance ( Shaped a, Shaped b, Shaped c, Shaped d, Shaped e, Shaped f
--          , Shaped g, Shaped h, Shaped i, Shaped j, Shaped k, Shaped l
--          , Shaped m, Shaped n, Shaped o, Shaped p, Shaped q, Shaped r
--          , Shaped s, Shaped t, Shaped u, Shaped v, Shaped w
--          ) => Shaped
--   (a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w)
-- instance ( Shaped a, Shaped b, Shaped c, Shaped d, Shaped e, Shaped f
--          , Shaped g, Shaped h, Shaped i, Shaped j, Shaped k, Shaped l
--          , Shaped m, Shaped n, Shaped o, Shaped p, Shaped q, Shaped r
--          , Shaped s, Shaped t, Shaped u, Shaped v, Shaped w, Shaped x
--           ) => Shaped
--   (a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x)
-- instance ( Shaped a, Shaped b, Shaped c, Shaped d, Shaped e, Shaped f
--          , Shaped g, Shaped h, Shaped i, Shaped j, Shaped k, Shaped l
--          , Shaped m, Shaped n, Shaped o, Shaped p, Shaped q, Shaped r
--          , Shaped s, Shaped t, Shaped u, Shaped v, Shaped w, Shaped x
--          , Shaped y
--          ) => Shaped
--   (a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y)
-- instance ( Shaped a, Shaped b, Shaped c, Shaped d, Shaped e, Shaped f
--          , Shaped g, Shaped h, Shaped i, Shaped j, Shaped k, Shaped l
--          , Shaped m, Shaped n, Shaped o, Shaped p, Shaped q, Shaped r
--          , Shaped s, Shaped t, Shaped u, Shaped v, Shaped w, Shaped x
--          , Shaped y, Shaped z
--          ) => Shaped
--   (a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z)
