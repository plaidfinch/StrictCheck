{-# LANGUAGE DefaultSignatures, TypeOperators, FlexibleContexts, FlexibleInstances #-}
module LazyCoArbitrary where

import GHC.Generics
import Test.QuickCheck

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




