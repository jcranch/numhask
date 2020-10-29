{-# LANGUAGE NegativeLiterals #-}
{-# LANGUAGE RebindableSyntax #-}
{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_HADDOCK prune #-}

-- | Numeric classes.
module NumHask
  ( -- * Usage
    -- $setup

    -- * Overview
    -- $overview
    -- $pictures

    -- * Prelude Mappings
    -- $mapping
    -- $backend

    -- * Extensions
    -- $extensions

    -- * Exports
    -- $instances
    module NumHask.Algebra.Abstract.Additive,
    module NumHask.Algebra.Abstract.Field,
    module NumHask.Algebra.Abstract.Group,
    module NumHask.Algebra.Abstract.Lattice,
    module NumHask.Algebra.Abstract.Module,
    module NumHask.Algebra.Abstract.Multiplicative,
    module NumHask.Algebra.Abstract.Ring,
    module NumHask.Analysis.Metric,
    module NumHask.Data.Complex,
    module NumHask.Data.Integral,
    module NumHask.Data.LogField,
    module NumHask.Data.Rational,
    module NumHask.Data.Pair,
    module NumHask.Data.Positive,
    module NumHask.Exception,

  )
where

import NumHask.Algebra.Abstract.Additive
import NumHask.Algebra.Abstract.Field
import NumHask.Algebra.Abstract.Group
import NumHask.Algebra.Abstract.Lattice
import NumHask.Algebra.Abstract.Module
import NumHask.Algebra.Abstract.Multiplicative
import NumHask.Algebra.Abstract.Ring
import NumHask.Analysis.Metric
import NumHask.Data.Complex
import NumHask.Data.Integral
import NumHask.Data.LogField
import NumHask.Data.Pair
import NumHask.Data.Positive
import NumHask.Data.Rational
import NumHask.Exception

-- $setup
--
-- >>> :set -XRebindableSyntax
-- >>> :set -XNegativeLiterals
-- >>> import NumHask.Prelude
-- >>> 1+1
-- 2
--
-- See the extensions section for discussion on recommended extensions.

-- $extensions
--
-- [RebindableSyntax](https://ghc.gitlab.haskell.org/ghc/doc/users_guide/exts/rebindable_syntax.html) and [NegativeLiterals](https://ghc.gitlab.haskell.org/ghc/doc/users_guide/exts/negative_literals.html) are both recommended for use with numhask. [LexicalNegation](https://ghc.gitlab.haskell.org/ghc/doc/users_guide/exts/lexical_negation.html) also looks sweet when it arrives.
--
-- As a replacement for the numerical classes in prelude, numhask clashes significantly with @import Prelude@. Either numhask modules should be qualified, or prelude turned off with the NoImplicitPrelude extension.
--
-- == defaulting
--
-- Without RebindableSyntax, numeric literals default as follows:
--
-- >>> :set -XNoRebindableSyntax
-- >>> :t 1
-- 1 :: Num p => p
--
-- >>> :t 1.0
-- 1.0 :: Fractional p => p
--
-- With RebindableSyntax (which also switches NoImplicitPrelude on) literal numbers change to numhask types:
--
-- >>> :set -XRebindableSyntax
-- >>> :t 1
-- 1 :: FromInteger a => a
--
-- >>> :t 1.0
-- 1.0 :: FromRational a => a
--
-- >>> 1
-- 1
--
-- >>> 1.0
-- 1.0
--
-- It is recommended to switch on RebindableSyntax to avoid Num constraints being introduced due to literal defaulting. The extension is a tradeoff, however, and usage comes attached with other non-numeric changes that "NumHask.Prelude" attempts to counteract.
--
-- See See [haskell2010 Section 4.3.4](https://www.haskell.org/onlinereport/haskell2010/haskellch4.html#x10-750004.3) for the nuts and bolts to defaulting.
--
-- The effect of [ExtendedDefaultRules](https://ghc.gitlab.haskell.org/ghc/doc/users_guide/ghci.html#extension-ExtendedDefaultRules) in ghci or switched on as an extension also need to be understood. It can lead to unusual interactions with numerics and strange error messages at times because it adds @()@ and @[]@ to the start of the type defaulting list.
--
-- == Negatives
--
-- Without [NegativeLiterals](https://ghc.gitlab.haskell.org/ghc/doc/users_guide/exts/negative_literals.html), GHC and Haskell often reads a negative as subtraction rather than a minus.
--
-- >>> :set -XNoNegativeLiterals
-- >>> :t Pair 1 -2
-- Pair 1 -2
--   :: (Subtractive (Pair a), FromInteger a,
--       FromInteger (a -> Pair a)) =>
--      a -> Pair a
-- ...
--
-- >>> :set -XNegativeLiterals
-- >>> :t Pair 1 -2
-- Pair 1 -2 :: FromInteger a => Pair a
--
-- >>> Pair 1 -2
-- Pair 1 -2
--
-- [LexicalNegation](https://ghc.gitlab.haskell.org/ghc/doc/users_guide/exts/lexical_negation.html) is coming soon as a valid replacement for NegativeLiterals and will tighten things up further.
--

-- $overview
-- numhask is largely a set of classes that can replace the 'GHC.Num.Num' class and it's descendents. Principles that have guided design include:
--
-- - _/middle-of-the-road class density/_. The numeric heirarchy begins with addition and multiplication, choosing not to build from a magma-base. Whilst not being as principled as other approaches, this circumvents the exponential instance growth problems of Haskell whilst maintaining clarity of class purpose.
--
-- - _/operator-first/_. In most cases, a class exists to define useful operators. There are exceptions, such as the 'Ring' class, that represent major conceptual domains.
--
-- - _/lawful/_. Most classes have laws associated with them that serve to relate class operators together in a meaningful way.
--
-- - _/low-impact/_. The library attempts to fit in with the rest of the Haskell ecosystem. It provides instances for common numbers: 'Int', 'Integer', 'Double', 'Float' and the Word number classes. It avoids name (or idea) clashes with other popular libraries and adopts conventions in the <https://hackage.haskell.org/package/base/docs/Prelude.html current prelude> where they make sense.
--
-- - _/proof-of-concept/_. The library may be below industrial-strength depending on a definition of this term. At the same time, most correspondence around improving the library is most welcome.

-- $pictures
--
-- The class heirarchy looks somewhat like this:
-- ![field example](other/field.svg)
--
-- The first two levels, Magma and it's direct descendents are "moral-only" and not  used in the subsequent class definitions so as to avoid naming clashes with base (Semigroup and Monoid), and instance explosion.
--

-- $mapping
--
-- 'GHC.Num' is a very old part of haskell, and is virtually unchanged since it's specification in [haskell98](https://www.haskell.org/onlinereport/standard-prelude.html).
--
-- 'GHC.Num.Num' is (very roughly) 'Ring'. Operators are split into 'Additive', 'Subtractive', 'Multiplicative' and 'Signed'. 'Distributive' is also introduced to cover distribution and absorption laws.
--
-- > -- | Basic numeric class.
-- > class  Num a  where
-- >    {-# MINIMAL (+), (*), abs, signum, fromInteger, (negate | (-)) #-}
-- >
-- >    (+), (-), (*)       :: a -> a -> a
-- >    -- | Unary negation.
-- >    negate              :: a -> a
--
-- + is a function of the 'Additive' class,
-- - & negate are functions in the 'Subtractive' class, and
-- * is a function of the 'Multiplicative' class.
--
-- >    -- | Absolute value.
-- >    abs                 :: a -> a
-- >    -- | Sign of a number.
-- >    -- The functions 'abs' and 'signum' should satisfy the law:
-- >    --
-- >    -- > abs x * signum x == x
-- >    --
-- >    -- For real numbers, the 'signum' is either @-1@ (negative), @0@ (zero)
-- >    -- or @1@ (positive).
-- >    signum              :: a -> a
--
-- abs is a function in the 'NumHask.Analysis.Metric.Signed' class.  The concept of an absolute value can also include situations where the domain and codomain are different, and 'norm' as a function in the 'NumHask.Analysis.Metric.Normed' class is supplied for these cases.
--
--  'NumHask.Analysis.Metric.sign' replaces 'signum', because signum is a heinous name.
--
-- >    -- | Conversion from an 'Integer'.
-- >    -- An integer literal represents the application of the function
-- >    -- 'fromInteger' to the appropriate value of type 'Integer',
-- >    -- so such literals have type @('Num' a) => a@.
-- >    fromInteger         :: Integer -> a
--
-- 'FromInteger' becomes its own class and 'FromIntegral' polymorphising the covariant.
--
-- 'GHC.Real.Integral' becomes 'Integral' and a polymorphic 'ToIntegral'.
-- 'GHC.Real.Fractional' becomes 'Field' and a polymorphic 'FromRatio'.
-- 'GHC.Real.RealFrac' becomes the polymorphic 'QuotientField'
-- 'GHC.Float.Floating' is split into 'ExpField' and 'TrigField'
-- 'GHC.Float.RealFloat' is not attempted. Life is too short.

-- $backend
-- NumHask imports Protolude as a starting prelude with some minor tweaks.
