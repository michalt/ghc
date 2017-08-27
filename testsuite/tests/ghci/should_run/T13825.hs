module T13825 where

import Data.Int
import Data.Word

data Packed =
    Packed
      {-# UNPACK #-} !Float
      {-# UNPACK #-} !Float
      {-# UNPACK #-} !Int8
      {-# UNPACK #-} !Word16
      {-# UNPACK #-} !Float
      {-# UNPACK #-} !Int
  deriving (Show)

packed1 = Packed 1.0 2.0 3 4 5 6

modAddOne :: Packed -> Packed
modAddOne (Packed a b c d e f) =
    Packed (a + 1.0) (b + 1.0) (c + 1) (d + 1) (e + 1.0) (f + 1)
