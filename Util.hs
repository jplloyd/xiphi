module Util where

surround :: String -> String -> String -> String
surround left right center = left ++ center ++ right

par :: String -> String 
par = surround "(" ")"

brace :: String -> String
brace = surround "{" "}"


-- This operation is unsafe
strip :: String -> String
strip = init . tail
