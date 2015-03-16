-- | Surface grammar which enforces the existence of implicit constructs
-- for every function type, lambda abstraction and application
module Surface where

import Util 
import Types

data SBind = SBind Name SExpr
data SAssign = SPos SExpr | SNamed Name SExpr

-- Expressions in the surface language
data SExpr = 
   SSet 
 | SCns Name
 | SVar Name
 | SFun [SBind] SBind SExpr 
 | SApp SExpr [SAssign] SExpr
 | SLam [Name] Name SExpr
 | SWld


-- Expression-construction helpers

set :: SExpr
set = SSet

constant :: Name -> SExpr
constant = SCns

function :: [SBind] -> SBind -> SExpr -> SExpr
function = SFun

function' :: SBind -> SExpr -> SExpr
function' = function []

apply :: SExpr -> [SAssign] -> SExpr -> SExpr
apply = SApp

apply' :: SExpr -> SExpr -> SExpr
apply' = flip apply []

lambda :: [Name] -> Name -> SExpr -> SExpr
lambda = SLam

lambda' :: Name -> SExpr -> SExpr
lambda' = SLam []

wildcard :: SExpr
wildcard = SWld

--

instance Show SExpr where
  show e' = case e' of 
   SSet -> "Set"
   SVar n -> n
   SCns n -> surround "<" ">"  n
   SFun impl expl cod -> pTele True impl ++ " " ++ pBind False expl ++ arrowRight ++ show cod
   SApp e1 impl e2 -> (show e1 ++ " " ++ pAssgn impl) ++ " " ++ par (show e2)
   SLam impl var e -> par $ "\\" ++ concatMap brace impl ++ " " ++ var ++ arrowRight ++ show e
   SWld -> "_"

instance Show SAssign where
  show e = brace $ case e of
    SPos e' -> show e'
    SNamed n e' -> n ++ ":=" ++ show e'

-- Print declared function telescope
pTele :: Bool -> [SBind] -> String
pTele impl = concatMap (pBind impl)

-- Print binds
pBind :: Bool -> SBind -> String
pBind True (SBind n e) = brace $ n ++ ":" ++ show e
pBind False (SBind n e) = par $ n ++ ":" ++ show e

-- Print list of impl arguments (given)
pAssgn :: [SAssign] -> String
pAssgn = unwords  . map show
