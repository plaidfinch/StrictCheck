{-# LANGUAGE DefaultSignatures, TypeOperators, FlexibleContexts, FlexibleInstances, ScopedTypeVariables, TypeApplications, TupleSections, BangPatterns #-}

{-# OPTIONS_GHC -fno-warn-unused-imports -fno-warn-type-defaults #-}

module Test.StrictCheck.Scratch.LazyCoArbitrary where

import GHC.Generics
import Test.QuickCheck
import Test.QuickCheck.Gen.Unsafe
import Data.Function
import Debug.Trace

class LazyCoArbitrary a where
  lazyCoarbitrary :: a -> Gen b -> Gen b
  default lazyCoarbitrary :: (Generic a, GLazyCoArbitrary (Rep a)) => a -> Gen b -> Gen b
  lazyCoarbitrary = genericLazyCoarbitrary

genericLazyCoarbitrary :: (Generic a, GLazyCoArbitrary (Rep a)) => a -> Gen b -> Gen b
genericLazyCoarbitrary = gLazyCoarbitrary . from

class GLazyCoArbitrary f where
  gLazyCoarbitrary :: f a -> Gen b -> Gen b

instance GLazyCoArbitrary U1 where
  gLazyCoarbitrary U1 = id

instance (GLazyCoArbitrary f, GLazyCoArbitrary g) => GLazyCoArbitrary (f :*: g) where
  gLazyCoarbitrary lr g =
    frequency [ (1, variant 0 g) -- Completely ignores the product
              , (1, let (l :*: r) = lr in variant 1 . gLazyCoarbitrary l . gLazyCoarbitrary r $ g)
              ]

instance (GLazyCoArbitrary f, GLazyCoArbitrary g) => GLazyCoArbitrary (f :+: g) where
  gLazyCoarbitrary lr g =
    frequency [ (1, variant 0 g) -- Completely lazy
              , (1, case lr of
                      L1 x -> variant 1 $ gLazyCoarbitrary x g
                      R1 x -> variant 2 $ gLazyCoarbitrary x g)
              ]

-- | TODO: Add laziness for these?
instance GLazyCoArbitrary f => GLazyCoArbitrary (M1 i c f) where
  gLazyCoarbitrary (M1 x) = gLazyCoarbitrary x

instance LazyCoArbitrary a => GLazyCoArbitrary (K1 i a) where
  gLazyCoarbitrary (K1 x) = lazyCoarbitrary x

{-
-- | Base instances - copy/pasted from coarbitrary
instance (Arbitrary a, LazyCoArbitrary b) => LazyCoArbitrary (a -> b) where
  lazyCoarbitrary f gen =
    do xs <- arbitrary
       lazyCoarbitrary (map f xs) gen

instance LazyCoArbitrary () where
  lazyCoarbitrary _ = id

instance LazyCoArbitrary Bool where
  lazyCoarbitrary False = variant 0
  lazyCoarbitrary True  = variant 1

instance LazyCoArbitrary Ordering where
  lazyCoarbitrary GT = variant 0
  lazyCoarbitrary EQ = variant 1
  lazyCoarbitrary LT = variant 2

instance LazyCoArbitrary a => LazyCoArbitrary (Maybe a) where
  lazyCoarbitrary Nothing  = variant 0
  lazyCoarbitrary (Just x) = variant 1 . lazyCoarbitrary x

instance (LazyCoArbitrary a, LazyCoArbitrary b) => LazyCoArbitrary (Either a b) where
  lazyCoarbitrary (Left x)  = variant 0 . lazyCoarbitrary x
  lazyCoarbitrary (Right y) = variant 1 . lazyCoarbitrary y

instance LazyCoArbitrary a => LazyCoArbitrary [a] where
  lazyCoarbitrary []     = variant 0
  lazyCoarbitrary (x:xs) = variant 1 . lazyCoarbitrary (x,xs)

instance (LazyCoArbitrary a, LazyCoArbitrary b)
      => LazyCoArbitrary (a,b)
 where
  lazyCoarbitrary (x,y) = lazyCoarbitrary x
                    . lazyCoarbitrary y

instance (LazyCoArbitrary a, LazyCoArbitrary b, LazyCoArbitrary c)
      => LazyCoArbitrary (a,b,c)
 where
  lazyCoarbitrary (x,y,z) = lazyCoarbitrary x
                      . lazyCoarbitrary y
                      . lazyCoarbitrary z

instance (LazyCoArbitrary a, LazyCoArbitrary b, LazyCoArbitrary c, LazyCoArbitrary d)
      => LazyCoArbitrary (a,b,c,d)
 where
  lazyCoarbitrary (x,y,z,v) = lazyCoarbitrary x
                        . lazyCoarbitrary y
                        . lazyCoarbitrary z
                        . lazyCoarbitrary v

instance (LazyCoArbitrary a, LazyCoArbitrary b, LazyCoArbitrary c, LazyCoArbitrary d, LazyCoArbitrary e)
      => LazyCoArbitrary (a,b,c,d,e)
 where
  lazyCoarbitrary (x,y,z,v,w) = lazyCoarbitrary x
                          . lazyCoarbitrary y
                          . lazyCoarbitrary z
                          . lazyCoarbitrary v
                          . lazyCoarbitrary w
-}

-- | Maybe extend this to Num? Probably will need UndecInstances
instance LazyCoArbitrary Int where
  lazyCoarbitrary = coarbitrary

-- | Temporary (?) Newtype hack to force our generation instead of the default coarbitrary
newtype LazyCoarb a = LazyCoarb {unLazy :: a}
  deriving (Show)

instance LazyCoArbitrary a => CoArbitrary (LazyCoarb a) where
  coarbitrary x g = lazyCoarbitrary (unLazy x) g

--------------------------
-- KENNY'S VERSION HERE --
--------------------------

-- TODO: replace with Produce/Consume

class ArbitraryK a where
  arbitraryK :: (a -> Gen b) -> Gen b

class CoArbitraryK a where
  coarbitraryK :: (a -> Gen b) -> (a -> Gen b)

instance ArbitraryK Integer where
  arbitraryK cont = do
    int <- arbitrary
    cont int

instance (ArbitraryK a, ArbitraryK b) => ArbitraryK (a, b) where
  arbitraryK cont =
    arbitraryK $ \a ->
      arbitraryK $ \b ->
        cont (a, b)

instance ArbitraryK a => ArbitraryK [a] where
  arbitraryK cont  =
    frequency [ (1,) $ cont []
              , (2,) $
                arbitraryK $ \first ->
                  arbitraryK $ \rest ->
                    cont $ first : rest
              ]

opaqueCoarbitraryK :: CoArbitrary a => (a -> Gen b) -> a -> Gen b
opaqueCoarbitraryK cont a =
  oneof [ variant 0 $ cont a
        , variant 1 $ coarbitrary a (cont a) ]

instance CoArbitraryK Integer where
  coarbitraryK = opaqueCoarbitraryK

instance (CoArbitraryK a, CoArbitraryK b) => CoArbitraryK (a, b) where
  coarbitraryK cont pair = do
    oneof [ variant 1 $ cont pair
          , variant 2 $ case pair of
              (a, b) ->
                oneof [ variant 3 $ coarbitraryK (\x -> cont (x, b)) a
                      , variant 4 $ coarbitraryK (\x -> cont (a, x)) b
                      ]
          ]

instance (CoArbitraryK a, CoArbitraryK b, CoArbitraryK c)
       => CoArbitraryK (a, b, c) where
  coarbitraryK cont triple = do
    oneof [ variant 1 $ cont triple
          , variant 2 $ case triple of
              (a, b, c) ->
                oneof [ variant 3 $
                        coarbitraryK (\(x, y) -> cont (x, y, c)) (a, b)
                      , variant 4 $
                        coarbitraryK (\(x, z) -> cont (x, b, z)) (a, c)
                      , variant 5 $
                        coarbitraryK (\(y, z) -> cont (a, y, z)) (b, c)
                      ]
          ]

instance (CoArbitraryK a) => CoArbitraryK [a] where
  coarbitraryK cont list = do
    oneof [ variant 1 $ cont list
          , variant 2 $ case list of
              [] -> cont []
              (a : as) ->
                oneof [ variant 3 $ coarbitraryK (\x  -> cont (x : as)) a
                      , variant 4 $ coarbitraryK (\xs -> cont (a : xs)) as
                      ]
          ]

-- lazyFunction :: forall x y. (CoArbitraryK x, ArbitraryK y) => Gen (x -> y)
-- lazyFunction = do
--   let transduce :: x -> Gen y
--       transduce x = coarbitraryK (\x' -> (_ (arbitraryK @y)) $ transduce x') x
--   promote transduce

-- lazyFunction :: forall a b. (CoArbitraryK a, ArbitraryK b) => Gen (a -> b)
-- lazyFunction = do
--   let destruct :: a -> Gen b =
--         coarbitraryK ((\a -> arbitraryK @b _) . destruct)
--   promote destruct
--   --return undefined
