-- | General utility functions - unorganized
module Util where

import Control.Monad.Except

surround :: String -> String -> String -> String
surround left right center = left ++ center ++ right

par :: String -> String 
par = surround "(" ")"

brace :: String -> String
brace = surround "{" "}"

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
