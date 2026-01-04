-- | Additive classes
module NumHask.Algebra.Additive
  ( Additive (..),
    Sum (..),
    sum,
    accsum,
    Subtractive (..),
    subtract,
    Subtractable (..),
    SubtractableTotal (..),
    SubtractablePositive (..),
  )
where

import Data.Int (Int16, Int32, Int64, Int8)
import Data.Maybe (isJust)
import Data.Semigroup (Semigroup (..))
import Data.Traversable (mapAccumL)
import Data.Word (Word, Word16, Word32, Word64, Word8)
import GHC.Natural (Natural (..))
import NumHask.Data.Interop (FromBase (..))
import Prelude (Bool(..), Double, Eq, Float, Int, Integer, Maybe(..), Ord(..), Show,
                fromInteger, otherwise, (<$>), (.), flip)
import Prelude qualified as P

-- $setup
--
-- >>> :m -Prelude
-- >>> :set -XRebindableSyntax
-- >>> import NumHask.Prelude

-- | or [Addition](https://en.wikipedia.org/wiki/Addition)
--
-- For practical reasons, we begin the class tree with 'NumHask.Algebra.Additive.Additive'.  Starting with  'NumHask.Algebra.Group.Associative' and 'NumHask.Algebra.Group.Unital', or using 'Data.Semigroup.Semigroup' and 'Data.Monoid.Monoid' from base tends to confuse the interface once you start having to disinguish between (say) monoidal addition and monoidal multiplication.
--
-- prop> \a -> zero + a == a
-- prop> \a -> a + zero == a
-- prop> \a b c -> (a + b) + c == a + (b + c)
-- prop> \a b -> a + b == b + a
--
-- By convention, (+) is regarded as commutative, but this is not universal, and the introduction of another symbol which means non-commutative addition seems a bit dogmatic.
--
-- >>> zero + 1
-- 1
--
-- >>> 1 + 1
-- 2
class Additive a where
  infixl 6 +
  (+) :: a -> a -> a

  zero :: a

-- | A wrapper for an Additive which distinguishes the additive structure
--
-- @since 0.11.1
newtype Sum a = Sum
  { getSum :: a
  }
  deriving (Eq, Ord, Show)

instance (Additive a) => P.Semigroup (Sum a) where
  Sum a <> Sum b = Sum (a + b)

instance (Additive a) => P.Monoid (Sum a) where
  mempty = Sum zero

deriving instance (Additive a) => Additive (Sum a)

-- | Compute the sum of a 'Data.Foldable.Foldable'.
--
-- >>> sum [0..10]
-- 55
sum :: (Additive a, P.Foldable f) => f a -> a
sum = getSum P.. P.foldMap Sum

-- | Compute the accumulating sum of a 'Data.Traversable.Traversable'.
--
-- >>> accsum [0..10]
-- [0,1,3,6,10,15,21,28,36,45,55]
accsum :: (Additive a, P.Traversable f) => f a -> f a
accsum = P.snd P.. mapAccumL (\a b -> (a + b, a + b)) zero

-- | or [Subtraction](https://en.wikipedia.org/wiki/Subtraction)
--
-- prop> \a -> a - a == zero
-- prop> \a -> negate a == zero - a
-- prop> \a -> negate a + a == zero
-- prop> \a -> a + negate a == zero
--
--
-- >>> negate 1
-- -1
--
-- >>> 1 - 2
-- -1
class Additive a => Subtractive a where

  negate :: a -> a
  negate a = zero - a

  infixl 6 -
  -- | Subtraction, with an error (usually Underflow) on failure
  (-) :: a -> a -> a
  a - b = a + negate b

  {-# MINIMAL (-) | negate #-}


-- | Flipped subtraction, useful for currying
-- >>> subtract 3 <$> [10,20,30]
-- [7,17,27]
subtract :: Subtractive a => a -> a -> a
subtract = flip (-)


-- | Subtraction with failure
--
-- We have a collection of methods to deal with the possibility that
-- subtraction might be a partial operation. We interpret these
-- methods as providing theoretical, rather than practical
-- information. For example, an Int8 represents numbers between -128
-- and 127, and therefore the subtraction (100)-(-100) will be
-- calculated incorrectly. However, we have 'subtractable 100 (-100)'
-- is 'True', because Int8 is a model of the integers (admittedly a
-- very imperfect model), and this subtraction can be performed in the
-- integers.
--
-- Nearly all Subtractive objects should be Subtractable: the
-- exceptions tend to be very large, like 'a -> b', where it is not
-- possable to tell whether there is a bad value or not.
--
-- Most Subtractable instances should be definable by "deriving
-- via".
class Subtractive a => Subtractable a where

  {-# MINIMAL (-?) | negateMaybe #-}

  -- | Subtraction, if possable
  infixl 6 -?
  (-?) :: a -> a -> Maybe a
  a -? b = (a +) <$> negateMaybe b

  -- | Negation, if possable
  negateMaybe :: a -> Maybe a
  negateMaybe = (zero -?)

  subtractable :: a -> a -> Bool
  subtractable x y = isJust (x -? y)

  negatable :: a -> Bool
  negatable = isJust . negateMaybe

-- | A wrapper to assist providing 'Subtractable' instances where
-- subtraction is total
newtype SubtractableTotal a = SubtractableTotal {
  getSubtractableTotal :: a
} deriving (Additive, Subtractive)

instance Subtractive a => Subtractable (SubtractableTotal a) where
  x -? y = Just (x - y)
  negateMaybe = Just . negate
  negatable _ = True
  subtractable _ _ = True

newtype SubtractablePositive a = SubtractablePositive {
  getSubtractablePositive :: a
} deriving (Additive, Eq, Ord, Subtractive)

instance (Ord a, Subtractive a) => Subtractable (SubtractablePositive a) where
  x -? y
    | x < y     = Nothing
    | otherwise = Just (x - y)
  negateMaybe x
    | x < zero  = Nothing
    | otherwise = Just (negate x)
  negatable x = x >= zero
  subtractable x y = x >= y


instance P.Num a => Additive (FromBase a) where
  FromBase x + FromBase y = FromBase (x P.+ y)
  zero = FromBase (P.fromInteger 0)

instance P.Num a => Subtractive (FromBase a) where
  FromBase x - FromBase y = FromBase (x P.- y)
  negate (FromBase x) = FromBase (P.negate x)


deriving via FromBase Double instance Additive Double
deriving via FromBase Double instance Subtractive Double
deriving via SubtractableTotal Double instance Subtractable Double

deriving via FromBase Float instance Additive Float
deriving via FromBase Float instance Subtractive Float
deriving via SubtractableTotal Float instance Subtractable Float

deriving via FromBase Int instance Additive Int
deriving via FromBase Int instance Subtractive Int
deriving via SubtractableTotal Int instance Subtractable Int

deriving via FromBase Integer instance Additive Integer
deriving via FromBase Integer instance Subtractive Integer
deriving via SubtractableTotal Integer instance Subtractable Integer


instance Additive Bool where
  (+) = (P.||)
  zero = P.False

deriving via FromBase Natural instance Additive Natural
deriving via FromBase Natural instance Subtractive Natural
deriving via SubtractablePositive Natural instance Subtractable Natural

deriving via FromBase Int8 instance Additive Int8
deriving via FromBase Int8 instance Subtractive Int8
deriving via SubtractableTotal Int8 instance Subtractable Int8

deriving via FromBase Int16 instance Additive Int16
deriving via FromBase Int16 instance Subtractive Int16
deriving via SubtractableTotal Int16 instance Subtractable Int16

deriving via FromBase Int32 instance Additive Int32
deriving via FromBase Int32 instance Subtractive Int32
deriving via SubtractableTotal Int32 instance Subtractable Int32

deriving via FromBase Int64 instance Additive Int64
deriving via FromBase Int64 instance Subtractive Int64
deriving via SubtractableTotal Int64 instance Subtractable Int64

deriving via FromBase Word instance Additive Word
deriving via FromBase Word instance Subtractive Word
deriving via SubtractablePositive Word instance Subtractable Word

deriving via FromBase Word8 instance Additive Word8
deriving via FromBase Word8 instance Subtractive Word8
deriving via SubtractablePositive Word8 instance Subtractable Word8

deriving via FromBase Word16 instance Additive Word16
deriving via FromBase Word16 instance Subtractive Word16
deriving via SubtractablePositive Word16 instance Subtractable Word16

deriving via FromBase Word32 instance Additive Word32
deriving via FromBase Word32 instance Subtractive Word32
deriving via SubtractablePositive Word32 instance Subtractable Word32

deriving via FromBase Word64 instance Additive Word64
deriving via FromBase Word64 instance Subtractive Word64
deriving via SubtractablePositive Word64 instance Subtractable Word64

instance (Additive b) => Additive (a -> b) where
  f + f' = \a -> f a + f' a
  zero _ = zero

instance (Subtractive b) => Subtractive (a -> b) where
  f - f' = \a -> f a - f' a
  negate f = negate . f
