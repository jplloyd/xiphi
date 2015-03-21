-- | General utility functions - unorganized
module Util where

import Data.List

import Control.Monad.Except

surround :: String -> String -> String -> String
surround left right center = left ++ center ++ right

par :: String -> String 
par = surround "(" ")"

brace :: String -> String
brace = surround "{" "}"

angBr :: String -> String
angBr = surround leftAngBr rightAngBr

brack :: String -> String
brack = surround "[" "]"

optMod :: (a -> Bool) -> (b -> b) -> (a -> b) -> a -> b
optMod p f shw a = (if p a then f . shw else shw) a

-- This operation is unsafe
strip :: String -> String
strip = init . tail


-- How do these functions not exist already?

-- | Nothing -> Left b
-- Just a -> Right (f a)
maybenot :: Maybe a -> (a -> c) -> b -> Either b c 
maybenot Nothing  _ b = Left b
maybenot (Just a) f _ = Right $ f a

-- maybenot in the Except monad
maybeErr :: Monad m => Maybe a -> (a -> c) -> b -> ExceptT b m c
maybeErr mb f e = case mb of
  Nothing -> throwError e
  Just a  -> return (f a)

-- probably replicating something more general here
-- zip which always retains the left list
maybezipR :: [a] -> [b] -> [(a,Maybe b)]
maybezipR [] _ = []
maybezipR xs [] = zip xs $ repeat Nothing
maybezipR (x:xs) (y:ys) = (x,Just y) : maybezipR xs ys

-- Check if the first list is a subsequence of the second
subsequence :: Eq a => [a] -> [a] -> Bool
subsequence _as _bs = go _as _bs
  where go [] _  = True
        go _  [] = False
        go (a:as) (b:bs) = if a == b then go as bs else go _as bs

-- Unicode strings

leftAngBr :: String
leftAngBr = "\10216"

rightAngBr :: String
rightAngBr = "\10217"

rightDblArr :: String
rightDblArr = "\8658 "

arrowLeft :: String
arrowLeft = "\8592 "

arrowRight :: String
arrowRight = " \8594 "
