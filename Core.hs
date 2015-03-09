{-# LANGUAGE FlexibleInstances#-}
module Core where

import Util
import Data.List

type Nm = String

data Ref = V Char Int -- V should not be used directly (note for export restrictions)

-- Variable reference
var :: Int -> Ref
var = V 'v'

-- Record binder reference
rec :: Int -> Ref
rec = V 'r'

type Field = String

newtype FList = FL {getList :: [Field]}

data CBind =
    CBind Field CExpr
  | CRef Ref CExpr

instance Show CBind where
  show (CBind f e) = par (f ++ " : " ++ show e)
  show (CRef r e)  = par (show r ++ " : " ++ show e)

data CAssign = CPos CExpr | CNamed Field CExpr

instance Show CAssign where
  show a = case a of
    CPos e -> brace (show e)
    CNamed f e -> brace (show f ++ ":=" ++ show e)

data CExpr = 
   CCns Nm                  -- Constant
 | CVar Ref                 -- Variable
 | CSet                     -- Type of types
 | CFun CBind CExpr         -- Dependent function type
 | CLam Ref FList Ref CExpr -- Lambda abstraction (bind, list of impl, expl bind, body)
 | CApp CExpr CExpr         -- Application
 | CSig [CBind]             -- Record type
 | CEStr [CAssign]          -- Expandable record
 | CProj CExpr Field        -- Projection
 | CWld                     -- Wildcard/underscore

data CSigma = CS [(Nm,CExpr)]

-- show instance for the expressions 
instance Show CExpr where
  show e' = case e' of 
    CCns n -> n
    CVar n -> show n
    CSet   -> "Set"
    CFun b e -> show b ++ " -> " ++ show e
    CLam r fs b e -> "\\" ++ par (show r ++ " : " ++ show fs) ++ show b ++ " -> " ++ show e
    CApp e1 e2 -> show e1 ++ " " ++ show e2
    CSig bs -> "sig" ++ brace (concatMap (strip . show) bs)
    CEStr asn -> "estr" ++ brace (intercalate "," (map (strip . show) asn))
    CProj e f -> show e ++"."++ show f
    CWld -> "_"

instance Show Ref where
  show (V c n) = c:cUnder n

instance Show CSigma where
  show (CS ls) = show ls

instance Show FList where
  show = concatMap (brace . show) . getList

-- I don't care about efficiency or elegance right now ↓

-- special conversion for numbering fields nicely

cUnder :: Int -> String
cUnder = map cUnd . show

-- Do I really have to do this manually? investigate in another life
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
  _   -> error "You cannot convert a non-numeric character using cUnd"
