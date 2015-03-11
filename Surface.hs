module Surface where

import Util 

type N = String

data SBind = SBind N SExpr
data SAssign = SPos SExpr | SNamed N SExpr

-- Expressions in the surface language
data SExpr = 
   SSet 
 | SCns N 
 | SVar N 
 | SFun [SBind] SBind SExpr 
 | SApp SExpr [SAssign] SExpr
 | SLam [N] N SExpr
 | SWld

data SSigma = SS [(N,SExpr)]

instance Show SExpr where
  show e' = case e' of 
   SSet -> "Set"
   SVar n -> n
   SCns n -> "Const_" ++ n
   SFun impl expl cod -> pTele True impl ++ " " ++ pBind False expl ++ arrowRight ++ show cod
   SApp e1 impl e2 -> unwords [show e1,pAssgn impl,show e2]
   SLam impl var e -> "\\" ++ concatMap brace impl ++ " " ++ var ++ arrowRight ++ show e
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
