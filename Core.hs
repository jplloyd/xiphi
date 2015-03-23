{-# LANGUAGE FlexibleInstances, RecordWildCards #-}
module Core where

import Util
import Types
import LatexPrint
import Data.List

newtype FList = FL {getList :: [Field]}

-- type bindings for variables and records
data CBind = CBind Ref CExpr

-- type bindings for record fields
data FBind = FBind Field CExpr

instance Show FBind where
  show (FBind f e) = par (f ++ " : " ++ show e)
  
instance Show CBind where
  show (CBind r e)  = par (show r ++ " : " ++ show e)

data CAssign = CPos CExpr | CNamed Field CExpr

-- get the field of the assignment (if it exists)
getAField :: CAssign -> Maybe Field
getAField (CPos _) = Nothing
getAField (CNamed f _) = Just f

-- get the expression of the assignment
getAExpr :: CAssign -> CExpr
getAExpr (CPos e) = e
getAExpr (CNamed _ e) = e

instance Show CAssign where
  show a = case a of
    CPos e -> brace (show e)
    CNamed f e -> brace (show f ++ ":=" ++ show e)

data CExpr = 
   CCns Name                -- Constant
 | CVar Ref                 -- Variable
 | CSet                     -- Type of types
 | CFun CBind CExpr         -- Dependent function type
 | CLam CBind CExpr         -- Lambda abstraction
 | CApp CExpr CExpr         -- Application
 | CSig [FBind]             -- Record type
 | CESig FList              -- Expandable sig
 | CEStr [CAssign]          -- Expandable struct
 | CProj CExpr Field        -- Projection
 | CWld                     -- Wildcard/underscore

data CSigma = CS [(Name,CExpr)]

-- show instance for the expressions 
instance Show CExpr where
  show e' = case e' of 
    CCns n -> n
    CVar n -> show n
    CSet   -> "Set"
    CFun b e -> show b ++ arrowRight ++ show e
    CLam b e -> par $ "\\" ++ show b ++ arrowRight ++ show e
    CApp e1 e2 -> par (show e1) ++ " " ++ show e2
    CSig bs -> "sig" ++ brace (concatMap (strip . show) bs)
    CESig fs -> "esig" ++ show fs
    CEStr asn -> "estr" ++ brace (intercalate "," (map (strip . show) asn))
    CProj e f -> show e ++"."++ f
    CWld -> "_"

needPar :: CExpr -> Bool
needPar e = case e of
  CApp{..} -> True
  CFun{..} -> True
  CLam{..} -> True
  _        -> False

instance Show CSigma where
  show (CS ls) = show ls

instance Show FList where
  show = concatMap (brace . show) . getList

instance LatexPrintable CExpr where
  latexPrint _e = case _e of
       CCns n -> ltx . mathit $ n
       CVar r -> lP r
       CSet -> ltx . mathit $ "Set"
       CFun cb e -> lP cb <++> ltxArr <++> lP e
       CLam cb e -> ltx "\\lambda" <©> lP cb <++> ltxArr <++> lP e
       CApp e1 e2 -> lP e1 <¢> optMod needPar lPar lP e2
       CSig fbs -> lLift (surround "\\sig{" "}") (lComma fbs)
       CESig fs -> lLift (surround "\\esig{" "}") (latexPrint fs)
       CEStr cas -> lLift (surround "\\estruct{" "}") $ lComma cas
       CProj e f -> lP e <++> ltx ("."++mathit f)
       CWld -> ltx "__"

instance LatexPrintable CBind where
  latexPrint (CBind r e) = lPar $ lP r <++> ltx " : " <++> lP e

instance LatexPrintable FBind where
  latexPrint (FBind f e) = ltx (mathit f) <++> ltx " : " <++> lP e

instance LatexPrintable CAssign where
  latexPrint ca = case ca of
    CPos e -> lP e
    CNamed f e -> ltx (f ++ " := ") <++> lP e

instance LatexPrintable FList where
  latexPrint (FL fs) = ltx . lBrace . intercalate ", " $ fs
  
