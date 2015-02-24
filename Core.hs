module Core where

import Util
import Data.List


type N = String
type F = String

data Bind = Bind N Expr

instance Show Bind where
  show (Bind n e) = par (n ++ " : " ++ show e)

data Assign = Pos Expr | Named F Expr

instance Show Assign where
  show a = case a of
    Pos e -> brace (show e)
    Named f e -> brace (f ++ ":=" ++ show e)

data Expr = 
   Cns N          -- Constant
 | Var N          -- Variable
 | Set            -- Type of types
 | Fun Bind Expr  -- Dependent function type
 | Lam Bind Expr  -- Lambda abstraction
 | App Expr Expr  -- Application
 | Sig [Bind]     -- Record type
 | LSig [F]       -- Unexpanded record type
 | EStr [Assign]  -- Expandable record
 | Proj Expr F    -- Projection
 | WCrd           -- Wildcard/underscore

data CSigma = CS [(N,Expr)]

-- show instance for the expressions 
instance Show Expr where
  show e' = case e' of 
    Cns n -> n
    Var n -> n
    Set   -> "Set"
    Fun b e -> show b ++ " -> " ++ show e
    Lam b e -> "\\" ++ show b ++ " -> " ++ show e
    App e1 e2 -> show e1 ++ " " ++ show e2
    Sig bs -> "sig" ++ brace (concatMap (strip . show) bs)
    LSig fs -> "lsig" ++ brace (intercalate "," fs)
    EStr asn -> "estr" ++ brace (intercalate "," (map (strip . show) asn))
    Proj e f -> show e ++"."++f
    WCrd -> "_"
