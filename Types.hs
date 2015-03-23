module Types where

import DList
import LatexPrint

import Control.Monad.Except
import Control.Monad.Trans.Writer

type Field = String
type Name = String
type Error = String
type Log = DList Char

type RuleIdx = Int


-- Error handling
type ErrT = ExceptT Error

-- Scope checking logging
type LogT = WriterT Log

-- #### Non-field bindings and references ####

data RefType = VarBind | RecBind | Unknown
  deriving (Eq,Ord,Show)

data Ref = V RefType Int
         | F String
  deriving (Eq,Ord,Show)

var :: Int -> Ref
var = V VarBind

rec :: Int -> Ref
rec = V RecBind

field :: String -> Ref
field = F

refBinding :: Ref -> String
refBinding = showRef

showRef :: Ref -> String
showRef (V c n) = toChar c:(map cUnd . show) n

toChar :: RefType -> Char
toChar b = case b of
  VarBind -> 'v'
  RecBind -> 'r'
  Unknown -> 'u'

-- Subscripted numerals
cUnd :: Char -> Char
cUnd c = case c of
  '0' -> '\8320'
  '1' -> '\8321'
  '2' -> '\8322'
  '3' -> '\8323'
  '4' -> '\8324'
  '5' -> '\8325'
  '6' -> '\8326'
  '7' -> '\8327'
  '8' -> '\8328'
  '9' -> '\8329'
  _   -> error "Only numeric characters may be subscripted"

-- ###########################################


instance LatexPrintable Ref where
  latexPrint r = case r of
    V rt n -> ltx $ toChar rt : "_" ++ show n
    F s -> ltx . mathit $ s
