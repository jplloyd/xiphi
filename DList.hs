module DList where

import Data.Monoid

-- Difference list - used for writing out the progress
newtype DList a = DL {getDlist :: [a] -> [a]}

fromDList :: DList a -> [a]
fromDList = ($ []) . getDlist

toDList :: [a] -> DList a
toDList ls = DL (ls++)

instance Monoid (DList a) where
  mempty = DL $ \xs -> [] ++ xs
  mappend d1 d2 = DL $ getDlist d1 . getDlist d2

instance Show a => Show (DList a) where
  show = show . fromDList
