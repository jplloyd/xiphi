{-# LANGUAGE RecordWildCards,  FlexibleInstances #-}
-- | Surface grammar which enforces the existence of implicit constructs
-- for every function type, lambda abstraction and application
module Surface where


import Data.List

import Util 
import Types
import LatexPrint

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
      SFun impl expl cod -> pTele True impl ++ pBind False expl ++ arrowRight ++ show cod
      SLam impl var e -> "\\" ++ concatMap (\b -> brace b ++ " ") impl ++ var ++ arrowRight ++ show e
      SApp e1 impl e2 -> show e1 ++ " " ++ pAssgn impl ++ mayPar e2
      SWld -> "_"
    where mayPar e = (if needPar e then par else id) (show e)

needPar :: SExpr -> Bool
needPar e = case e of
  SFun{..} -> True -- illegal, but not enforced
  SApp{..} -> True
  SLam{..} -> True -- also illegal b.n.e
  _        -> False

instance Show SAssign where
  show e = brace $ case e of
    SPos e' -> show e'
    SNamed n e' -> n ++ " := " ++ show e'

-- Print declared function telescope
pTele :: Bool -> [SBind] -> String
pTele impl = concatMap (\b -> pBind impl b ++ " ")

-- Print binds
pBind :: Bool -> SBind -> String
pBind True (SBind n e) = brace $ n ++ " : " ++ show e
pBind False (SBind n e) = par $ n ++ " : " ++ show e

-- Print list of impl arguments (given)
pAssgn :: [SAssign] -> String
pAssgn = unwords . map (\a -> show a ++ " ")

-- Latex printing

instance LatexPrintable SExpr where
  latexPrint _e = case _e of
    SSet -> ltx . mathit $ "Set"
    SCns n -> ltx . mathit $ n
    SVar n -> ltx . mathit $ n
    SFun imp expl e -> lLift lBrace (lP imp) <©> lLift par (lP expl) <++> ltxArr <++> lP e
    SApp e1 as e2 -> lP e1 <¢> lP as <¢> optMod needPar (lLift par) lP e2
    SLam imps expl e -> ltx ("\\lambda " ++ lBrace (intercalate ", " imps) ++ " " ++ expl)
                        <++> ltx " -> " <++> latexPrint e
    SWld -> ltx "__"

instance LatexPrintable SBind where
  latexPrint (SBind n e) = lLift ((mathit n ++ " : ")++) (lP e)

instance LatexPrintable [SBind]
  where latexPrint sbs = foldr (<++>) (ltx "") (intersperse (ltx ", ") (map lP sbs))

instance LatexPrintable SAssign where
  latexPrint sa = case sa of
    SPos e -> lP e
    SNamed n e -> ltx (n ++ " := ") <++> lP e

instance LatexPrintable [SAssign] where
  latexPrint sbs = lLift lBrace $ foldr (<++>) (ltx "") (intersperse (ltx ", ") (map lP sbs))
