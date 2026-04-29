-- | Classes for interoperability with Haskell's base library
module NumHask.Data.Interop
  ( FromBase (..),
    ToBase (..),
  )
where

import Prelude (Enum, Eq, Ord)


-- | A wrapper for putting NumHask instances on types with base
-- numeric instances
newtype FromBase a = FromBase {
  getFromBase :: a
} deriving (Enum, Eq, Ord)

-- | A wrapper for putting base instances on types with NumHask
-- numeric instances; to avoid orphan instances, we'll have to
-- repeatedly define other versions of this.
newtype ToBase a = ToBase {
  getToBase :: a
} deriving (Enum, Eq, Ord)
