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

-- Unicode stuff

-- useless, but diacritics are cool
vectorify :: String -> String
vectorify s = intersperse '\773' s ++ "\773" -- "\8407"

leftAngBr :: String
leftAngBr = "\10216"

rightAngBr :: String
rightAngBr = "\10217"

rightDblArr :: String
rightDblArr = "\8658 "
