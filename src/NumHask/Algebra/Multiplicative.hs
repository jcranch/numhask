-- | Multiplicative classes
module NumHask.Algebra.Multiplicative
  ( Multiplicative (..),
    Product (..),
    product,
    accproduct,
    Divisive (..),
    Divisible (..),
    DivisibleTotal (..),
    DivisibleField (..),
    DivisibleDivMod (..),
  )
where

import Control.Exception (ArithException(..), throw)
import Data.Int (Int16, Int32, Int64, Int8)
import Data.Maybe (isJust)
import Data.Traversable (mapAccumL)
import Data.Word (Word, Word16, Word32, Word64, Word8)
import GHC.Natural (Natural (..))
import NumHask.Algebra.Additive (Additive(..))
import NumHask.Data.Interop (FromBase (..))
import Prelude (Double, Eq(..), Float, Int, Integer, Bool(..), Maybe(..), Ord, Show, fromInteger, otherwise, (<$>), (.))
import Prelude qualified as P

-- $setup
--
-- >>> :m -Prelude
-- >>> :set -XRebindableSyntax
-- >>> import NumHask.Prelude

-- | or [Multiplication](https://en.wikipedia.org/wiki/Multiplication)
--
-- For practical reasons, we begin the class tree with 'NumHask.Algebra.Additive.Additive' and 'Multiplicative'.  Starting with  'NumHask.Algebra.Group.Associative' and 'NumHask.Algebra.Group.Unital', or using 'Data.Semigroup.Semigroup' and 'Data.Monoid.Monoid' from base tends to confuse the interface once you start having to disinguish between (say) monoidal addition and monoidal multiplication.
--
--
-- prop> \a -> one * a == a
-- prop> \a -> a * one == a
-- prop> \a b c -> (a * b) * c == a * (b * c)
--
-- By convention, (*) is regarded as not necessarily commutative, but this is not universal, and the introduction of another symbol which means commutative multiplication seems a bit dogmatic.
--
-- >>> one * 2
-- 2
--
-- >>> 2 * 3
-- 6
class Multiplicative a where
  infixl 7 *
  (*) :: a -> a -> a

  one :: a

-- | A wrapper for an Multiplicative which distinguishes the multiplicative structure
--
-- @since 0.11.1
newtype Product a = Product
  { getProduct :: a
  }
  deriving (Eq, Ord, Show)

instance (Multiplicative a) => P.Semigroup (Product a) where
  Product a <> Product b = Product (a * b)

instance (Multiplicative a) => P.Monoid (Product a) where
  mempty = Product one

-- | Compute the product of a 'Data.Foldable.Foldable'.
--
-- >>> product [1..5]
-- 120
product :: (Multiplicative a, P.Foldable f) => f a -> a
product = getProduct . P.foldMap Product

-- | Compute the accumulating product of a 'Data.Traversable.Traversable'.
--
-- >>> accproduct [1..5]
-- [1,2,6,24,120]
accproduct :: (Multiplicative a, P.Traversable f) => f a -> f a
accproduct = P.snd . mapAccumL (\a b -> (a * b, a * b)) one

-- | or [Division](https://en.wikipedia.org/wiki/Division_(mathematics\))
--
-- Though unusual, the term Divisive usefully fits in with the grammer of other classes and avoids name clashes that occur with some popular libraries.
--
-- prop> \(a :: Double) -> a / a ~= one || a == zero
-- prop> \(a :: Double) -> recip a ~= one / a || a == zero
-- prop> \(a :: Double) -> recip a * a ~= one || a == zero
-- prop> \(a :: Double) -> a * recip a ~= one || a == zero
--
-- >>> recip 2.0
-- 0.5
--
-- >>> 1 / 2
-- 0.5
class (Multiplicative a) => Divisive a where
  {-# MINIMAL (/) | recip #-}

  recip :: a -> a
  recip a = one / a

  infixl 7 /

  (/) :: a -> a -> a
  (/) a b = a * recip b


-- | A class representing the fact that division is very frequently a
-- partial operation, comparable to MaybeSubtractive.
--
-- Most Divisive instances should also be Divisible.
class Divisive a => Divisible a where

  {-# MINIMAL (/?) | recipMaybe #-}

  -- | Subtraction, if possible
  infixl 6 /?
  (/?) :: a -> a -> Maybe a
  a /? b = (a *) <$> recipMaybe b

  -- | Negation, if possible
  recipMaybe :: a -> Maybe a
  recipMaybe = (one /?)

  divisible :: a -> a -> Bool
  divisible x y = isJust (x /? y)

  invertible :: a -> Bool
  invertible = isJust . recipMaybe


newtype DivisibleTotal a = DivisibleTotal {
  getDivisibleTotal :: a
} deriving (Eq, Ord, Multiplicative, Divisive)

instance Divisible a => Divisible (DivisibleTotal a) where
  x /? y = Just (x / y)
  recipMaybe x = Just (recip x)
  divisible _ _ = True
  invertible _ = True


newtype DivisibleField a = DivisibleField {
  getDivisibleField :: a
} deriving (Eq, Ord, Additive, Multiplicative, Divisive)

instance (Additive a, Divisible a, Eq a) => Divisible (DivisibleField a) where
  x /? y
    | y == zero = Nothing
    | otherwise = Just (x/y)
  recipMaybe x
    | x == zero = Nothing
    | otherwise = Just (recip x)
  divisible _ = (/= zero)
  invertible = (/= zero)


newtype DivisibleDivMod a = DivisibleDivMod {
  getDivisibleDivMod :: a
} deriving (Eq, Ord, Additive, Multiplicative, P.Num, P.Enum, P.Real, P.Integral)

instance (Additive a, Divisible a, P.Integral a) => Divisive (DivisibleDivMod a) where
  x / y = case x /? y of
    Just q -> q
    Nothing -> throw DivideByZero
  recip x = case recipMaybe x of
    Just y -> y
    Nothing -> throw DivideByZero

instance (Additive a, Divisible a, P.Integral a) => Divisible (DivisibleDivMod a) where
  x /? y
    | r == zero = Just q
    | otherwise = Nothing where
        (q,r) = P.divMod x y
  divisible x y = P.mod x y == zero


instance P.Num a => Multiplicative (FromBase a) where
  FromBase x * FromBase y = FromBase (x P.* y)
  one = FromBase (P.fromInteger 1)

instance P.Fractional a => Divisive (FromBase a) where
  FromBase x / FromBase y = FromBase (x P./ y)
  recip (FromBase x) = FromBase (P.recip x)


deriving via FromBase Double instance Multiplicative Double
deriving via FromBase Double instance Divisive Double
deriving via DivisibleField Double instance Divisible Double

deriving via FromBase Float instance Multiplicative Float
deriving via FromBase Float instance Divisive Float
deriving via DivisibleField Float instance Divisible Float

deriving via FromBase Int instance Multiplicative Int
deriving via DivisibleDivMod Int instance Divisive Int
deriving via DivisibleDivMod Int instance Divisible Int

deriving via FromBase Integer instance Multiplicative Integer
deriving via DivisibleDivMod Integer instance Divisive Integer
deriving via DivisibleDivMod Integer instance Divisible Integer

instance Multiplicative P.Bool where
  (*) = (P.&&)
  one = P.True

deriving via FromBase Natural instance Multiplicative Natural
deriving via DivisibleDivMod Natural instance Divisive Natural
deriving via DivisibleDivMod Natural instance Divisible Natural

deriving via FromBase Int8 instance Multiplicative Int8
deriving via DivisibleDivMod Int8 instance Divisive Int8
deriving via DivisibleDivMod Int8 instance Divisible Int8

deriving via FromBase Int16 instance Multiplicative Int16
deriving via DivisibleDivMod Int16 instance Divisive Int16
deriving via DivisibleDivMod Int16 instance Divisible Int16

deriving via FromBase Int32 instance Multiplicative Int32
deriving via DivisibleDivMod Int32 instance Divisive Int32
deriving via DivisibleDivMod Int32 instance Divisible Int32

deriving via FromBase Int64 instance Multiplicative Int64
deriving via DivisibleDivMod Int64 instance Divisive Int64
deriving via DivisibleDivMod Int64 instance Divisible Int64

deriving via FromBase Word instance Multiplicative Word
deriving via DivisibleDivMod Word instance Divisive Word
deriving via DivisibleDivMod Word instance Divisible Word

deriving via FromBase Word8 instance Multiplicative Word8
deriving via DivisibleDivMod Word8 instance Divisive Word8
deriving via DivisibleDivMod Word8 instance Divisible Word8

deriving via FromBase Word16 instance Multiplicative Word16
deriving via DivisibleDivMod Word16 instance Divisive Word16
deriving via DivisibleDivMod Word16 instance Divisible Word16

deriving via FromBase Word32 instance Multiplicative Word32
deriving via DivisibleDivMod Word32 instance Divisive Word32
deriving via DivisibleDivMod Word32 instance Divisible Word32

deriving via FromBase Word64 instance Multiplicative Word64
deriving via DivisibleDivMod Word64 instance Divisive Word64
deriving via DivisibleDivMod Word64 instance Divisible Word64

instance (Multiplicative b) => Multiplicative (a -> b) where
  (f * f') a = f a * f' a
  one _ = one

instance (Divisive b) => Divisive (a -> b) where
  (f / f') a = f a / f' a
  recip f = recip . f
