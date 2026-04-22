{-# LANGUAGE DefaultSignatures #-}

-- | [field](https://en.wikipedia.org/wiki/Field_(mathematics\)) classes
module NumHask.Algebra.Field
  ( SemiField,
    Field,
    ExpField (..),
    infinity,
    negInfinity,
    nan,
    TrigField (..),
    half,
    Roundable (..),
    round,
    truncate,
    floor,
    ceiling,
  )
where

import Data.Bool (bool)
import NumHask.Algebra.Additive (Additive (..), Subtractive (..), (-))
import NumHask.Algebra.Multiplicative
  ( Divisive (..),
    Multiplicative (..),
    (/),
  )
import NumHask.Algebra.Ring
  ( Distributive,
    Ring,
    two,
  )
import NumHask.Data.Integral
  ( Rounding,
    ToMinusInfty (..),
    ToPlusInfty (..),
    ToZero (..),
    ToNearest (..),
  )
import NumHask.Data.Interop
  ( FromBase (..),
  )
import Prelude
  ( Ord (..),
    Bool (..),
    (.),
    (<$>),
  )
import Prelude qualified as P

-- $setup
--
-- >>> :m -Prelude
-- >>> :set -XRebindableSyntax
-- >>> :set -XScopedTypeVariables
-- >>> import NumHask.Prelude

-- | A <https://en.wikipedia.org/wiki/Semifield Semifield> is a field with no subtraction.
--
-- @since 0.12
type SemiField a = (Distributive a, Divisive a)

-- | A <https://en.wikipedia.org/wiki/Field_(mathematics) Field> is a set
--   on which addition, subtraction, multiplication, and division are defined. It is also assumed that multiplication is distributive over addition.
--
-- A summary of the rules inherited from super-classes of Field:
--
-- > zero + a == a
-- > a + zero == a
-- > ((a + b) + c) (a + (b + c))
-- > a + b == b + a
-- > a - a == zero
-- > negate a == zero - a
-- > negate a + a == zero
-- > a + negate a == zero
-- > one * a == a
-- > a * one == a
-- > ((a * b) * c) == (a * (b * c))
-- > (a * (b + c)) == (a * b + a * c)
-- > ((a + b) * c) == (a * c + b * c)
-- > a * zero == zero
-- > zero * a == zero
-- > a / a == one || a == zero
-- > recip a == one / a || a == zero
-- > recip a * a == one || a == zero
-- > a * recip a == one || a == zero
type Field a = (Ring a, Divisive a)

-- | A hyperbolic field class
--
-- prop> \(a::Double) -> a < zero || (sqrt . (**2)) a == a
-- prop> \(a::Double) -> a < zero || (log . exp) a ~= a
-- prop> \(a::Double) (b::Double) -> (b < zero) || a <= zero || a == 1 || abs (a ** logBase a b - b) < 10 * epsilon
class
  (Field a) =>
  ExpField a
  where
  exp :: a -> a
  log :: a -> a
  (**) :: a -> a -> a
  (**) a b = exp (log a * b)

  -- | log to the base of
  --
  -- >>> logBase 2 8
  -- 2.9999999999999996
  logBase :: a -> a -> a
  logBase a b = log b / log a

  -- | square root
  --
  -- >>> sqrt 4
  -- 2.0
  sqrt :: a -> a
  sqrt a = a ** (one / (one + one))

instance ExpField P.Double where
  exp = P.exp
  log = P.log
  (**) = (P.**)

instance ExpField P.Float where
  exp = P.exp
  log = P.log
  (**) = (P.**)

instance (ExpField b) => ExpField (a -> b) where
  exp f = exp . f
  log f = log . f


-- | Numbers that can be rounded
class Rounding r => Roundable r i a where

  roundingWithRemainder :: r -> a -> (i, a)

  rounding :: r -> a -> i
  rounding r x = P.fst (roundingWithRemainder r x)


properFraction :: Roundable ToZero i a => a -> (i, a)
properFraction = roundingWithRemainder ToZero

truncate :: Roundable ToZero i a => a -> i
truncate = rounding ToZero

round :: Roundable ToNearest i a => a -> i
round = rounding ToNearest

ceiling :: Roundable ToPlusInfty i a => a -> i
ceiling = rounding ToPlusInfty

floor :: Roundable ToMinusInfty i a => a -> i
floor = rounding ToMinusInfty

instance P.RealFrac a => Roundable ToZero P.Int (FromBase a) where
  roundingWithRemainder _ (FromBase x) = FromBase <$> P.properFraction x
  rounding _ (FromBase x) = P.truncate x

-- | A class used to define other roundings from ToZero by newtype deriving
newtype FromTruncate a = FromTruncate a

instance (Ord i, Ord a, Ring i, Ring a, Roundable ToZero i a) => Roundable ToNearest i (FromTruncate a) where
  roundingWithRemainder _ (FromTruncate x)
    | x >= zero = bool (q, FromTruncate r) (q+one, FromTruncate (r-one)) (x+x > one)
    | True = bool (q, FromTruncate r) (q-one, FromTruncate (r+one)) (x+x <= negate one) where
        (q,r) = properFraction x

instance (Ord i, Ord a, Ring i, Ring a, Roundable ToZero i a) => Roundable ToMinusInfty i (FromTruncate a) where
  roundingWithRemainder _ (FromTruncate x)
    | x >= zero = (q, FromTruncate r)
    | r < zero = (q-one, FromTruncate (r+one))
    | True = (q, FromTruncate r) where
        (q,r) = properFraction x

instance (Ord i, Ord a, Ring i, Ring a, Roundable ToZero i a) => Roundable ToPlusInfty i (FromTruncate a) where
  roundingWithRemainder _ (FromTruncate x)
    | x <= zero = (q, FromTruncate r)
    | r > zero = (q+one, FromTruncate (r-one))
    | True = (q, FromTruncate r) where
        (q,r) = properFraction x

deriving via FromBase P.Float instance Roundable ToZero P.Int P.Float
deriving via FromBase P.Double instance Roundable ToZero P.Int P.Double

deriving via FromTruncate P.Float instance Roundable ToNearest P.Int P.Float
deriving via FromTruncate P.Double instance Roundable ToNearest P.Int P.Double

deriving via FromTruncate P.Float instance Roundable ToMinusInfty P.Int P.Float
deriving via FromTruncate P.Double instance Roundable ToMinusInfty P.Int P.Double

deriving via FromTruncate P.Float instance Roundable ToPlusInfty P.Int P.Float
deriving via FromTruncate P.Double instance Roundable ToPlusInfty P.Int P.Double

-- | infinity is defined for any 'Field'.
--
-- >>> one / zero + infinity
-- Infinity
--
-- >>> infinity + 1
-- Infinity
infinity :: (SemiField a) => a
infinity = one / zero

-- | nan is defined as zero/zero
--
-- but note the (social) law:
--
-- >>> nan == zero / zero
-- False
nan :: (SemiField a) => a
nan = zero / zero

-- | negative infinity
--
-- >>> negInfinity + infinity
-- NaN
negInfinity :: (Field a) => a
negInfinity = negate infinity

-- | Trigonometric Field
--
-- The list of laws is quite long: <https://en.wikipedia.org/wiki/List_of_trigonometric_identities trigonometric identities>
class
  (Field a) =>
  TrigField a
  where
  pi :: a
  sin :: a -> a
  cos :: a -> a
  tan :: a -> a
  tan x = sin x / cos x
  asin :: a -> a
  acos :: a -> a
  atan :: a -> a
  atan2 :: a -> a -> a
  sinh :: a -> a
  cosh :: a -> a
  tanh :: a -> a
  tanh x = sinh x / cosh x
  asinh :: a -> a
  acosh :: a -> a
  atanh :: a -> a

instance TrigField P.Double where
  pi = P.pi
  sin = P.sin
  cos = P.cos
  asin = P.asin
  acos = P.acos
  atan = P.atan
  atan2 = P.atan2
  sinh = P.sinh
  cosh = P.cosh
  asinh = P.asinh
  acosh = P.acosh
  atanh = P.atanh

instance TrigField P.Float where
  pi = P.pi
  sin = P.sin
  cos = P.cos
  asin = P.asin
  acos = P.acos
  atan = P.atan
  atan2 = P.atan2
  sinh = P.sinh
  cosh = P.cosh
  asinh = P.asinh
  acosh = P.acosh
  atanh = P.atanh

instance (TrigField b) => TrigField (a -> b) where
  pi _ = pi
  sin f = sin . f
  cos f = cos . f
  asin f = asin . f
  acos f = acos . f
  atan f = atan . f
  atan2 f g x = atan2 (f x) (g x)
  sinh f = sinh . f
  cosh f = cosh . f
  asinh f = asinh . f
  acosh f = acosh . f
  atanh f = atanh . f

-- | A half of 'one'
--
-- >>> half :: Double
-- 0.5
half :: (Additive a, Divisive a) => a
half = one / two
