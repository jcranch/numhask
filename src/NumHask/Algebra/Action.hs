-- | Algebra for Actions
--
-- Convention: the |'s in the operators point towards the higher-kinded number, representing an operator or action __into__ a structure.
module NumHask.Algebra.Action
  ( AdditiveAction (..),
    SubtractiveAction (..),
    (-|),
    MultiplicativeAction (..),
    DivisiveAction (..),
    (/|),
    Module,
    TrivialAction (..),
  )
where

import NumHask.Algebra.Additive (Additive(..), Subtractive(..))
import NumHask.Algebra.Multiplicative (Divisive(..), Multiplicative(..))
import NumHask.Algebra.Ring (Distributive)
import Prelude (flip, Eq, Ord)

-- | Additive Action
--
-- > m |+ zero == m
-- > zero +| m == m
class
  Additive s => AdditiveAction s m | m -> s
  where

  infixl 6 |+
  (|+) :: m -> s -> m
  (|+) = flip (+|)

  infixl 6 +|
  (+|) :: s -> m -> m
  (+|) = flip (|+)

  {-# MINIMAL (|+) | (+|) #-}

-- | Subtractive Action
--
-- > m |- zero = m
class
  (AdditiveAction s m, Subtractive s) =>
  SubtractiveAction s m | m -> s
  where
  infixl 6 |-
  (|-) :: m -> s -> m

infixl 6 -|

-- | Subtraction with the scalar on the left
--
-- > (-|) == (+|) . negate
-- > zero -| m = negate m
(-|) :: (AdditiveAction s m, Subtractive m) => s -> m -> m
a -| b = a +| negate b

-- | Multiplicative Action
--
-- > m |* one = m
-- > one *| m = one
class
  (Multiplicative s) =>
  MultiplicativeAction s m | m -> s
  where

  infixl 7 |*
  (|*) :: m -> s -> m
  (|*) = flip (*|)

  infixl 7 *|
  (*|) :: s -> m -> m
  (*|) = flip (|*)

  {-# MINIMAL (|*) | (*|) #-}

-- | Divisive Action
--
-- > m |/ one = m
class
  (Divisive s, MultiplicativeAction s m) =>
  DivisiveAction s m
  where
  infixl 7 |/
  (|/) :: m -> s -> m

-- | left scalar division
--
-- > (/|) == (*|) . recip
-- > one |/ m = recip m
(/|) :: (MultiplicativeAction s m, Divisive m) => s -> m -> m
a /| b = a *| recip b

-- | A <https://en.wikipedia.org/wiki/Module_(mathematics) Module>
--
-- > a *| one == a
-- > (a + b) *| c == (a *| c) + (b *| c)
-- > c |* (a + b) == (c |* a) + (c |* b)
-- > a *| zero == zero
-- > a *| b == b |* a
type Module s m = (Distributive s, MultiplicativeAction s m)

-- | An action of a set of numbers on itself
newtype TrivialAction a = TrivialAction {
  getTrivialAction :: a
} deriving (Eq, Ord, Additive, Subtractive, Multiplicative, Divisive)

instance Additive a => AdditiveAction a (TrivialAction a) where
  TrivialAction a |+ b = TrivialAction (a + b)
  a +| TrivialAction b = TrivialAction (a + b)

instance Subtractive a => SubtractiveAction a (TrivialAction a) where
  TrivialAction a |- b = TrivialAction (a - b)

instance Multiplicative a => MultiplicativeAction a (TrivialAction a) where
  TrivialAction a |* b = TrivialAction (a * b)
  a *| TrivialAction b = TrivialAction (a * b)

instance Divisive a => DivisiveAction a (TrivialAction a) where
  TrivialAction a |/ b = TrivialAction (a / b)
