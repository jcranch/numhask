-- | Multiplicative classes
module NumHask.Algebra.Multiplicative
  ( Multiplicative (..),
    Product (..),
    product,
    accproduct,
    Divisive (..),
  )
where

import Data.Int (Int16, Int32, Int64, Int8)
import Data.Traversable (mapAccumL)
import Data.Word (Word, Word16, Word32, Word64, Word8)
import GHC.Natural (Natural (..))
import NumHask.Data.Interop (FromBase (..))
import Prelude (Double, Eq, Float, Int, Integer, Ord, Show, fromInteger)
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
product = getProduct P.. P.foldMap Product

-- | Compute the accumulating product of a 'Data.Traversable.Traversable'.
--
-- >>> accproduct [1..5]
-- [1,2,6,24,120]
accproduct :: (Multiplicative a, P.Traversable f) => f a -> f a
accproduct = P.snd P.. mapAccumL (\a b -> (a * b, a * b)) one

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

instance P.Num a => Multiplicative (FromBase a) where
  FromBase x * FromBase y = FromBase (x P.* y)
  one = FromBase (P.fromInteger 1)

instance P.Fractional a => Divisive (FromBase a) where
  FromBase x / FromBase y = FromBase (x P./ y)
  recip (FromBase x) = FromBase (P.recip x)

deriving via FromBase Double instance Multiplicative Double
deriving via FromBase Double instance Divisive Double

deriving via FromBase Float instance Multiplicative Float
deriving via FromBase Float instance Divisive Float

deriving via FromBase Int instance Multiplicative Int

deriving via FromBase Integer instance Multiplicative Integer

instance Multiplicative P.Bool where
  (*) = (P.&&)
  one = P.True

deriving via FromBase Natural instance Multiplicative Natural

deriving via FromBase Int8 instance Multiplicative Int8

deriving via FromBase Int16 instance Multiplicative Int16

deriving via FromBase Int32 instance Multiplicative Int32

deriving via FromBase Int64 instance Multiplicative Int64

deriving via FromBase Word instance Multiplicative Word

deriving via FromBase Word8 instance Multiplicative Word8

deriving via FromBase Word16 instance Multiplicative Word16

deriving via FromBase Word32 instance Multiplicative Word32

deriving via FromBase Word64 instance Multiplicative Word64

instance (Multiplicative b) => Multiplicative (a -> b) where
  f * f' = \a -> f a * f' a
  one _ = one

instance (Divisive b) => Divisive (a -> b) where
  recip f = recip P.. f
