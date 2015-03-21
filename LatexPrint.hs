{-# LANGUAGE RecordWildCards #-}
module LatexPrint where

import Util

newtype Latex = Latex String

instance Show Latex where
  show (Latex s) = s

(<++>) :: Latex -> Latex -> Latex
(Latex a) <++> (Latex b) = Latex $ a ++ b

(<©>) :: Latex -> Latex -> Latex
(Latex a) <©> (Latex b) = Latex $ a ++ " " ++ b

(<¢>) :: Latex -> Latex -> Latex
(Latex a) <¢> (Latex b) = Latex $ a ++ " \\fsp " ++ b

         
lLift :: (String -> String) -> Latex -> Latex
lLift f (Latex s) = Latex (f s) 

ltx :: String -> Latex
ltx = Latex

ltxArr :: Latex
ltxArr = ltx " -> "

class LatexPrintable a where
  latexPrint :: a -> Latex

lP :: LatexPrintable a => a -> Latex
lP = latexPrint

mathit :: String -> String
mathit n = "\\mathit{" ++ n ++ "}"

lBrace :: String -> String
lBrace n = "\\sbrace{" ++ n ++ "}"
