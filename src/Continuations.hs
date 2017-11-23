
{-# LANGUAGE TypeApplications, TupleSections, DeriveAnyClass, DeriveGeneric #-}

module Continuations where

import Control.Monad
import Control.Monad.Trans
import Control.Monad.Trans.Cont
import Test.QuickCheck
import qualified Test.QuickCheck.Gen.Unsafe as Unsafe
import Data.Function
import Control.Spoon
import Data.List
import Control.Applicative
import Data.Foldable
import Data.Maybe
import Control.DeepSeq
import GHC.Generics
import Data.IORef
import System.IO.Unsafe as Unsafe
import Data.Bool

import Observe

-- Playing around with continuations

m1, m2 :: (Integer -> ContT r IO Integer) -> Integer -> ContT r IO Integer

m1 _ 0 = return 0
m1 k i = do
  liftIO . putStrLn $ "i = " ++ show i
  j <- k (i - 1)
  liftIO . putStrLn $ show (i + j) ++ " = " ++ show i ++ " + " ++ show j
  return (i + j)

m2 _ 0 = return 1
m2 k i = do
  liftIO . putStrLn $ "i = " ++ show i
  j <- k (i - 1)
  liftIO . putStrLn $ show (i * j) ++ " = " ++ show i ++ " * " ++ show j
  return (i * j)


----------------------------------------------------------
-- Experiments in generating random functions over nats --
----------------------------------------------------------

data Nat = Z | S Nat deriving (Eq, Ord, Generic, NFData)

natNum :: Nat -> Integer
natNum Z = 0
natNum (S n) = succ (natNum n)

numNat :: Integer -> Nat
numNat n | n <= 0    = Z
         | otherwise = S (numNat (pred n))

instance Num Nat where
  fromInteger = numNat
  a + b = numNat $ natNum a + natNum b
  a - b = numNat $ natNum a - natNum b
  a * b = numNat $ natNum a * natNum b
  abs = id
  signum 0 = 0
  signum n = 1

instance Show Nat where
  show = show . natNum

instance Enum Nat where
  fromEnum n = fromInteger $ natNum n
  toEnum i = numNat (toInteger i)

{-# NOINLINE instrumentNat #-}
instrumentNat :: IORef Integer -> Nat -> Nat
instrumentNat count n =
  unsafePerformIO $
    case n of
      Z    -> modifyIORef' count succ >> return Z
      S n' -> modifyIORef' count succ >> return (S $ instrumentNat count n')

{-# NOINLINE natFunctionDemand #-}
natFunctionDemand :: (Nat -> ()) -> (Nat -> Nat) -> Nat -> Integer
natFunctionDemand c f input =
  unsafePerformIO $ do
    count <- newIORef 0
    let result = f $ instrumentNat count input
    evaluate (c result)
    forced <- readIORef count
    return forced

nStrict :: Integer -> Nat -> ()
nStrict 0 _ = ()
nStrict i n =
  case n of
    Z -> ()
    S n' -> nStrict (pred i) n'

natDemands :: (Nat -> Nat) -> [[Integer]]
natDemands f =
  let c = continuity f in
  flip map [0..c] $ \input ->
    flip map [0..f (numNat input) + 1] $ \demand ->
      natFunctionDemand (nStrict (natNum demand)) f (numNat input)

-- must produce exactly one constructor of output
natProduce :: Gen Nat -> Gen Nat
natProduce gen =
  frequency [ (1,) $ variant 1 $ return Z
            , (2,) $ variant 2 $ S <$> gen
            ]

-- must consume either zero or one constructors of input
natConsume :: (Gen Nat -> Gen Nat) -> Nat -> Gen Nat
natConsume produce nat =
  frequency [ (1,) $ variant 1 $ produce (natConsume produce nat)
            , (1,) $ variant 2 $
                case nat of
                  Z      -> variant 3 $ fix produce
                  S nat' -> variant 4 $ produce (natConsume produce nat')
            ]

natFunction :: Gen (Nat -> Nat)
natFunction = Unsafe.promote $ natConsume natProduce

nats, partialNats :: [Nat]
nats        = iterate S Z
partialNats = iterate S undefined

continuity :: (Nat -> Nat) -> Integer
continuity f =
  genericLength . takeWhile isNothing $
    map (spoon . f) partialNats

undefinedAt :: Integer -> Nat
undefinedAt 0 = undefined
undefinedAt n = S (undefinedAt (pred n))

prettyNatFunction :: (Nat -> Nat) -> IO ()
prettyNatFunction f = do
  let inputs = genericTake (c + 1) nats
      c      = continuity f
      demands = natDemands f
      demandBehaviors =
        flip map demands $ \list ->
          map ((0 ==) . uncurry (-)) $
            zip list (tail list)
      showBehavior n bs acc =
        case bs of
          [] -> reverse acc
          (b : bs') ->
            if b then showBehavior n bs' (" ~" ++ acc)
            else case n of
              Z   -> showBehavior n bs' (" Z" ++ acc)
              S n' -> showBehavior n' bs' (" S" ++ acc)

  putStrLn $ "\n  Continuity: " ++ show c ++ "\n"
  putStrLn $ "  Input  |  Output  |  Demand Behavior"
  putStrLn $ "---------+----------+-------------------"
  forM_ (zip inputs demandBehaviors) $ \(input, behavior) ->
    putStrLn $ "    "
            ++ show input
            ++ replicate (5 - (length $ show input)) ' ' ++ "|    "
            ++ show (f input)
            ++ replicate (6 - (length $ show (f input))) ' ' ++ "|  "
            ++ showBehavior input behavior ""
  putStrLn $ "    ⋮    |    ⋮     |  "
          ++ intercalate " " (replicate (length (last demandBehaviors)) "⋮") ++ "\n"

prettyRandomNatFunction :: IO (Nat -> Nat)
prettyRandomNatFunction = do
  f <- generate natFunction
  prettyNatFunction f
  return f
