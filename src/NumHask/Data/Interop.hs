-- | Classes for interoperability with Haskell's base library
module NumHask.Data.Interop
  ( FromBase (..),
    ToBase (..),
  )
where

import Prelude (Eq, Ord)


-- | A wrapper for putting NumHask instances on types with base
-- numeric instances
newtype FromBase a = FromBase {
  getFromBase :: a
} deriving (Eq, Ord)

-- | A wrapper for putting base instances on types with NumHask
-- numeric instances
newtype ToBase a = ToBase {
  getToBase :: a
} deriving (Eq, Ord)
