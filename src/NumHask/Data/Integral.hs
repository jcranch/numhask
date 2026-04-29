-- | Integral classes
module NumHask.Data.Integral
  ( Rounding,
    ToZero (..),
    ToMinusInfty (..),
    ToPlusInfty (..),
    ToNearest (..),
    Remaindered (..),
    div,
    mod,
    divMod,
    quot,
    rem,
    quotRem,
    Integral,
    FullIntegral,
    NonnegativeIntegral,
    ToIntegral (..),
    ToInt,
    FromIntegral (..),
    FromInt,
    FromInteger (..),
    ToInteger (..),
    even,
    odd,
    (^^),
    (^),
    ToBaseIntegral (..),
    )
where

import Data.Int (Int16, Int32, Int64, Int8)
import Data.Ord
import Data.Ratio qualified as P
import Data.Word (Word, Word16, Word32, Word64, Word8)
import GHC.Natural (Natural (..), naturalFromInteger)
import NumHask.Algebra.Additive
import NumHask.Algebra.Multiplicative
import NumHask.Algebra.Ring
import NumHask.Data.Interop (FromBase (..))
import Prelude (Double, Enum(..), Eq(..), Float, Int, Integer, error, fst, snd, (.))
import Prelude qualified as P


-- | A rounding convention
class Rounding r

-- | Rounding towards zero
data ToZero = ToZero
instance Rounding ToZero

-- | Rounding towards minus infinity
data ToMinusInfty = ToMinusInfty
instance Rounding ToMinusInfty

-- | Rounding towards plus infinity
data ToPlusInfty = ToPlusInfty
instance Rounding ToPlusInfty

-- | Rounding to the nearest integer
data ToNearest = ToNearest
instance Rounding ToNearest


-- | A Remaindered must satisfy the law
--
-- prop> \r a b -> b == zero || b * quotient r a b + remainder r a b == a
class Rounding r => Remaindered r t where

  quotient :: r -> t -> t -> t
  quotient r x y = fst (quotientRemainder r x y)

  remainder :: r -> t -> t -> t
  remainder r x y = snd (quotientRemainder r x y)

  quotientRemainder :: r -> t -> t -> (t, t)
  quotientRemainder r x y = (quotient r x y, remainder r x y)

  {-# MINIMAL (quotient, remainder) | quotientRemainder #-}

div :: Remaindered ToMinusInfty t => t -> t -> t
div = quotient ToMinusInfty

mod :: Remaindered ToMinusInfty t => t -> t -> t
mod = remainder ToMinusInfty

divMod :: Remaindered ToMinusInfty t => t -> t -> (t, t)
divMod = quotientRemainder ToMinusInfty

quot :: Remaindered ToZero t => t -> t -> t
quot = quotient ToZero

rem :: Remaindered ToZero t => t -> t -> t
rem = remainder ToZero

quotRem :: Remaindered ToZero t => t -> t -> (t, t)
quotRem = quotientRemainder ToZero


instance P.Integral a => Remaindered ToMinusInfty (FromBase a) where
  quotient _ (FromBase x) (FromBase y) = FromBase (P.div x y)
  remainder _ (FromBase x) (FromBase y) = FromBase (P.mod x y)
  quotientRemainder _ (FromBase x) (FromBase y) = let
    (q,r) = P.divMod x y
    in (FromBase q, FromBase r)

instance P.Integral a => Remaindered ToZero (FromBase a) where
  quotient _ (FromBase x) (FromBase y) = FromBase (P.quot x y)
  remainder _ (FromBase x) (FromBase y) = FromBase (P.rem x y)
  quotientRemainder _ (FromBase x) (FromBase y) = let
    (q,r) = P.quotRem x y
    in (FromBase q, FromBase r)

newtype FromMinusInfty a = FromMinusInfty a

instance (P.Eq a, Ring a, Remaindered ToMinusInfty a) => Remaindered ToPlusInfty (FromMinusInfty a) where
  quotientRemainder _ (FromMinusInfty x) (FromMinusInfty y)
    | r P.== zero = (FromMinusInfty q, FromMinusInfty r)
    | P.True = (FromMinusInfty (q + one), FromMinusInfty (r - y)) where
        (q, r) = quotientRemainder ToMinusInfty x y
  remainder _ (FromMinusInfty x) (FromMinusInfty y)
    | r P.== zero = FromMinusInfty r
    | P.True = FromMinusInfty (r - y) where
        r = remainder ToMinusInfty x y

instance (Ord a, Ring a, Remaindered ToMinusInfty a) => Remaindered ToNearest (FromMinusInfty a) where
  quotientRemainder _ (FromMinusInfty x) (FromMinusInfty y)
    | r + r > y = (FromMinusInfty (q + one), FromMinusInfty (r - y))
    | P.True = (FromMinusInfty q, FromMinusInfty r) where
        (q, r) = quotientRemainder ToMinusInfty x y
  remainder _ (FromMinusInfty x) (FromMinusInfty y)
    | r + r > y = FromMinusInfty (r - y)
    | P.True = FromMinusInfty r where
        r = remainder ToMinusInfty x y

deriving via FromBase Int instance Remaindered ToMinusInfty Int
deriving via FromBase Int instance Remaindered ToZero Int
deriving via FromMinusInfty Int instance Remaindered ToPlusInfty Int
deriving via FromMinusInfty Int instance Remaindered ToNearest Int

deriving via FromBase Integer instance Remaindered ToMinusInfty Integer
deriving via FromBase Integer instance Remaindered ToZero Integer
deriving via FromMinusInfty Integer instance Remaindered ToPlusInfty Integer
deriving via FromMinusInfty Integer instance Remaindered ToNearest Integer

deriving via FromBase Natural instance Remaindered ToMinusInfty Natural
deriving via FromBase Natural instance Remaindered ToZero Natural
deriving via FromMinusInfty Natural instance Remaindered ToPlusInfty Natural
deriving via FromMinusInfty Natural instance Remaindered ToNearest Natural

deriving via FromBase Int8 instance Remaindered ToMinusInfty Int8
deriving via FromBase Int8 instance Remaindered ToZero Int8
deriving via FromMinusInfty Int8 instance Remaindered ToPlusInfty Int8
deriving via FromMinusInfty Int8 instance Remaindered ToNearest Int8

deriving via FromBase Int16 instance Remaindered ToMinusInfty Int16
deriving via FromBase Int16 instance Remaindered ToZero Int16
deriving via FromMinusInfty Int16 instance Remaindered ToPlusInfty Int16
deriving via FromMinusInfty Int16 instance Remaindered ToNearest Int16

deriving via FromBase Int32 instance Remaindered ToMinusInfty Int32
deriving via FromBase Int32 instance Remaindered ToZero Int32
deriving via FromMinusInfty Int32 instance Remaindered ToPlusInfty Int32
deriving via FromMinusInfty Int32 instance Remaindered ToNearest Int32

deriving via FromBase Int64 instance Remaindered ToMinusInfty Int64
deriving via FromBase Int64 instance Remaindered ToZero Int64
deriving via FromMinusInfty Int64 instance Remaindered ToPlusInfty Int64
deriving via FromMinusInfty Int64 instance Remaindered ToNearest Int64

deriving via FromBase Word instance Remaindered ToMinusInfty Word
deriving via FromBase Word instance Remaindered ToZero Word
deriving via FromMinusInfty Word instance Remaindered ToPlusInfty Word
deriving via FromMinusInfty Word instance Remaindered ToNearest Word

deriving via FromBase Word8 instance Remaindered ToMinusInfty Word8
deriving via FromBase Word8 instance Remaindered ToZero Word8
deriving via FromMinusInfty Word8 instance Remaindered ToPlusInfty Word8
deriving via FromMinusInfty Word8 instance Remaindered ToNearest Word8

deriving via FromBase Word16 instance Remaindered ToMinusInfty Word16
deriving via FromBase Word16 instance Remaindered ToZero Word16
deriving via FromMinusInfty Word16 instance Remaindered ToPlusInfty Word16
deriving via FromMinusInfty Word16 instance Remaindered ToNearest Word16

deriving via FromBase Word32 instance Remaindered ToMinusInfty Word32
deriving via FromBase Word32 instance Remaindered ToZero Word32
deriving via FromMinusInfty Word32 instance Remaindered ToPlusInfty Word32
deriving via FromMinusInfty Word32 instance Remaindered ToNearest Word32

deriving via FromBase Word64 instance Remaindered ToMinusInfty Word64
deriving via FromBase Word64 instance Remaindered ToZero Word64
deriving via FromMinusInfty Word64 instance Remaindered ToPlusInfty Word64
deriving via FromMinusInfty Word64 instance Remaindered ToNearest Word64


instance Remaindered r b => Remaindered r (a -> b) where
  quotient r f g x = quotient r (f x) (g x)
  remainder r f g x = remainder r (f x) (g x)


-- | This is used for types which model the naturals or integers.
--
-- The Integral class in the base prelude is extremely vague about
-- what it's to be used for, which is dangerous: it's simultaneously
-- possible to assume that it's only to be used for things very
-- similar to the integers, and also to put instances of it for other
-- things with division with remainder. So, for example, a^b is
-- defined for any integral type, and one could put an Integral
-- instance on the Gaussian integers and attempt to evaluate 3^i.
--
-- We thus give classes with much more precise uses.
class (Ord a, Ring a, FromInteger a, ToInteger a, Remaindered ToMinusInfty a, Remaindered ToZero a) => Integral a where

-- | This is used for types which model the integers.
class Integral a => FullIntegral a where

-- | This is used for types which model the naturals.
class Integral a => NonnegativeIntegral a where


instance P.Num a => FromInteger (FromBase a) where
  fromInteger = FromBase . P.fromInteger


instance P.Integral a => Integral (FromBase a) where


-- | This is used for defining base prelude numerical types
newtype ToBaseIntegral a = ToBaseIntegral {
  getBaseIntegral :: a
} deriving (Eq, Ord, Remaindered r, FromInteger, ToInteger)


instance (FromInteger a, Ring a) => P.Num (ToBaseIntegral a) where
  ToBaseIntegral a + ToBaseIntegral b = ToBaseIntegral (a + b)
  ToBaseIntegral a - ToBaseIntegral b = ToBaseIntegral (a - b)
  negate (ToBaseIntegral a) = ToBaseIntegral (negate a)
  ToBaseIntegral a * ToBaseIntegral b = ToBaseIntegral (a * b)
  fromInteger = ToBaseIntegral . fromInteger
  abs = error "Our implementation of Num for NumHask Rings doesn't define abs"
  signum = error "Our implementation of Num for NumHask Rings doesn't define signum"


instance (FromInteger a, ToInteger a, Ring a) => Enum (ToBaseIntegral a) where
  toEnum = fromInteger . fromIntegral
  fromEnum = toIntegral . toInteger
  succ (ToBaseIntegral a) = ToBaseIntegral (a+one)
  pred (ToBaseIntegral a) = ToBaseIntegral (a-one)


instance (FromInteger a, ToInteger a, Integral a, Ord a) => P.Real (ToBaseIntegral a) where
  toRational (ToBaseIntegral a) = toInteger a P.% 1


instance (FromInteger a, ToInteger a, Integral a, Ord a) => P.Integral (ToBaseIntegral a) where
  toInteger = toInteger
  quot = quot
  rem = rem
  quotRem = quotRem
  div = div
  mod = mod
  divMod = divMod


instance Integral Integer
instance FullIntegral Integer

instance Integral Int
instance FullIntegral Int

instance Integral Int8
instance FullIntegral Int8

instance Integral Int16
instance FullIntegral Int16

instance Integral Int32
instance FullIntegral Int32

instance Integral Int64
instance FullIntegral Int64

instance Integral Natural
instance NonnegativeIntegral Natural

instance Integral Word
instance NonnegativeIntegral Word

instance Integral Word8
instance NonnegativeIntegral Word8

instance Integral Word16
instance NonnegativeIntegral Word16

instance Integral Word32
instance NonnegativeIntegral Word32

instance Integral Word64
instance NonnegativeIntegral Word64


-- |
-- >>> even 2
-- True
even :: (Integral a) => a -> P.Bool
even n = n `rem` (one + one) P.== zero

-- |
-- >>> odd 3
-- True
odd :: (Integral a) => a -> P.Bool
odd = P.not . even


-- | toIntegral is kept separate from Integral to help with compatibility issues.
--
-- > toIntegral a == a
class ToIntegral a b where
  {-# MINIMAL toIntegral #-}

  toIntegral :: a -> b

-- | Convert to an 'Int'
type ToInt a = ToIntegral a Int

instance ToIntegral Integer Integer where
  toIntegral = P.id

instance ToIntegral Int Integer where
  toIntegral = P.toInteger

instance ToIntegral Natural Integer where
  toIntegral = P.toInteger

instance ToIntegral Int8 Integer where
  toIntegral = P.toInteger

instance ToIntegral Int16 Integer where
  toIntegral = P.toInteger

instance ToIntegral Int32 Integer where
  toIntegral = P.toInteger

instance ToIntegral Int64 Integer where
  toIntegral = P.toInteger

instance ToIntegral Word Integer where
  toIntegral = P.toInteger

instance ToIntegral Word8 Integer where
  toIntegral = P.toInteger

instance ToIntegral Word16 Integer where
  toIntegral = P.toInteger

instance ToIntegral Word32 Integer where
  toIntegral = P.toInteger

instance ToIntegral Word64 Integer where
  toIntegral = P.toInteger

instance ToIntegral Int Int where
  toIntegral = P.id

instance ToIntegral Integer Int where
  toIntegral = P.fromIntegral

instance ToIntegral Natural Int where
  toIntegral = P.fromIntegral

instance ToIntegral Int8 Int where
  toIntegral = P.fromIntegral

instance ToIntegral Int16 Int where
  toIntegral = P.fromIntegral

instance ToIntegral Int32 Int where
  toIntegral = P.fromIntegral

instance ToIntegral Int64 Int where
  toIntegral = P.fromIntegral

instance ToIntegral Word Int where
  toIntegral = P.fromIntegral

instance ToIntegral Word8 Int where
  toIntegral = P.fromIntegral

instance ToIntegral Word16 Int where
  toIntegral = P.fromIntegral

instance ToIntegral Word32 Int where
  toIntegral = P.fromIntegral

instance ToIntegral Word64 Int where
  toIntegral = P.fromIntegral

instance ToIntegral Natural Natural where
  toIntegral = P.id

instance ToIntegral Int8 Int8 where
  toIntegral = P.id

instance ToIntegral Int16 Int16 where
  toIntegral = P.id

instance ToIntegral Int32 Int32 where
  toIntegral = P.id

instance ToIntegral Int64 Int64 where
  toIntegral = P.id

instance ToIntegral Word Word where
  toIntegral = P.id

instance ToIntegral Word8 Word8 where
  toIntegral = P.id

instance ToIntegral Word16 Word16 where
  toIntegral = P.id

instance ToIntegral Word32 Word32 where
  toIntegral = P.id

instance ToIntegral Word64 Word64 where
  toIntegral = P.id

-- | Polymorphic version of fromInteger
--
-- > fromIntegral a == a
class FromIntegral a b where
  {-# MINIMAL fromIntegral #-}

  fromIntegral :: b -> a

-- | Convert from an 'Int'
type FromInt a = FromIntegral a Int

instance (FromIntegral a b) => FromIntegral (c -> a) b where
  fromIntegral i _ = fromIntegral i

instance FromIntegral Double Integer where
  fromIntegral = P.fromInteger

instance FromIntegral Float Integer where
  fromIntegral = P.fromInteger

instance FromIntegral Int Integer where
  fromIntegral = P.fromInteger

instance FromIntegral Integer Integer where
  fromIntegral = P.id

instance FromIntegral Natural Integer where
  fromIntegral = naturalFromInteger

instance FromIntegral Int8 Integer where
  fromIntegral = P.fromInteger

instance FromIntegral Int16 Integer where
  fromIntegral = P.fromInteger

instance FromIntegral Int32 Integer where
  fromIntegral = P.fromInteger

instance FromIntegral Int64 Integer where
  fromIntegral = P.fromInteger

instance FromIntegral Word Integer where
  fromIntegral = P.fromInteger

instance FromIntegral Word8 Integer where
  fromIntegral = P.fromInteger

instance FromIntegral Word16 Integer where
  fromIntegral = P.fromInteger

instance FromIntegral Word32 Integer where
  fromIntegral = P.fromInteger

instance FromIntegral Word64 Integer where
  fromIntegral = P.fromInteger

instance FromIntegral Double Int where
  fromIntegral = P.fromIntegral

instance FromIntegral Float Int where
  fromIntegral = P.fromIntegral

instance FromIntegral Int Int where
  fromIntegral = P.id

instance FromIntegral Integer Int where
  fromIntegral = P.fromIntegral

instance FromIntegral Natural Int where
  fromIntegral = P.fromIntegral

instance FromIntegral Int8 Int where
  fromIntegral = P.fromIntegral

instance FromIntegral Int16 Int where
  fromIntegral = P.fromIntegral

instance FromIntegral Int32 Int where
  fromIntegral = P.fromIntegral

instance FromIntegral Int64 Int where
  fromIntegral = P.fromIntegral

instance FromIntegral Word Int where
  fromIntegral = P.fromIntegral

instance FromIntegral Word8 Int where
  fromIntegral = P.fromIntegral

instance FromIntegral Word16 Int where
  fromIntegral = P.fromIntegral

instance FromIntegral Word32 Int where
  fromIntegral = P.fromIntegral

instance FromIntegral Word64 Int where
  fromIntegral = P.fromIntegral

instance FromIntegral Natural Natural where
  fromIntegral = P.id

instance FromIntegral Int8 Int8 where
  fromIntegral = P.id

instance FromIntegral Int16 Int16 where
  fromIntegral = P.id

instance FromIntegral Int32 Int32 where
  fromIntegral = P.id

instance FromIntegral Int64 Int64 where
  fromIntegral = P.id

instance FromIntegral Word Word where
  fromIntegral = P.id

instance FromIntegral Word8 Word8 where
  fromIntegral = P.id

instance FromIntegral Word16 Word16 where
  fromIntegral = P.id

instance FromIntegral Word32 Word32 where
  fromIntegral = P.id

instance FromIntegral Word64 Word64 where
  fromIntegral = P.id


-- | 'fromInteger' is special in two ways:
--
-- - numeric integral literals (like "42") are interpreted specifically as "fromInteger (42 :: GHC.Num.Integer)". The prelude version is used as default (or whatever fromInteger is in scope if RebindableSyntax is set).
--
-- - The default rules in < https://www.haskell.org/onlinereport/haskell2010/haskellch4.html#x10-750004.3 haskell2010> specify that constraints on 'fromInteger' need to be in a form @C v@, where v is a Num or a subclass of Num.
--
-- So a type synonym such as @type FromInteger a = FromIntegral a Integer@ doesn't work well with type defaulting; hence the need for a separate class.
class FromInteger a where
  fromInteger :: Integer -> a

instance FromInteger Double where
  fromInteger = P.fromInteger

instance FromInteger Float where
  fromInteger = P.fromInteger

instance FromInteger Int where
  fromInteger = P.fromInteger

instance FromInteger Integer where
  fromInteger = P.id

instance FromInteger Natural where
  fromInteger = naturalFromInteger

instance FromInteger Int8 where
  fromInteger = P.fromInteger

instance FromInteger Int16 where
  fromInteger = P.fromInteger

instance FromInteger Int32 where
  fromInteger = P.fromInteger

instance FromInteger Int64 where
  fromInteger = P.fromInteger

instance FromInteger Word where
  fromInteger = P.fromInteger

instance FromInteger Word8 where
  fromInteger = P.fromInteger

instance FromInteger Word16 where
  fromInteger = P.fromInteger

instance FromInteger Word32 where
  fromInteger = P.fromInteger

instance FromInteger Word64 where
  fromInteger = P.fromInteger

deriving instance FromInteger a => FromInteger (Sum a)

deriving instance FromInteger a => FromInteger (Product a)


-- | A ToIntegral specialised to Integer, to help with typing
class ToInteger a where
  toInteger :: a -> Integer

instance P.Integral a => ToInteger (FromBase a) where
  toInteger (FromBase a) = P.toInteger a

deriving via FromBase Integer instance ToInteger Integer
deriving via FromBase Int instance ToInteger Int
deriving via FromBase Int8 instance ToInteger Int8
deriving via FromBase Int16 instance ToInteger Int16
deriving via FromBase Int32 instance ToInteger Int32
deriving via FromBase Int64 instance ToInteger Int64
deriving via FromBase Natural instance ToInteger Natural
deriving via FromBase Word instance ToInteger Word
deriving via FromBase Word8 instance ToInteger Word8
deriving via FromBase Word16 instance ToInteger Word16
deriving via FromBase Word32 instance ToInteger Word32
deriving via FromBase Word64 instance ToInteger Word64



infixr 8 ^^

-- | raise a number to an 'Integral' power
--
-- >>> 2 ^^ 3
-- 8.0
--
-- >>> 2 ^^ (-2)
-- 0.25
(^^) ::
  (Divisive a, Integral b) =>
  a ->
  b ->
  a
x0 ^^ y0 =
  case compare y0 zero of
    EQ -> one
    GT -> f x0 y0
    LT -> recip (x0 ^^ negate y0)
  where
    f x y
      | even y = f (x * x) (y `quot` two)
      | y P.== one = x
      | P.otherwise = g (x * x) (y `quot` two) x
    g x y z
      | even y = g (x * x) (y `quot` two) z
      | y P.== one = x * z
      | P.otherwise = g (x * x) (y `quot` two) (x * z)

infixr 8 ^

-- | raise a number to an 'Int' power
--
-- Note: This differs from (^) found in prelude which is a partial function (it errors on negative integrals). This is a monomorphic version of '(^^)' provided to help reduce ambiguous type noise in common usages.
--
-- >>> 2 ^ 3
-- 8.0
--
-- >>> 2 ^ (-2)
-- 0.25
(^) ::
  (Divisive a) => a -> Int -> a
(^) x n = x ^^ n
