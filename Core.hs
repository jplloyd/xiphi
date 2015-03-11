{-# LANGUAGE FlexibleInstances#-}
module Core where

import Util
import Types
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
 | CLam Ref FList Ref CExpr -- Lambda abstraction (bind, list of impl, expl bind, body)
 | CApp CExpr CExpr         -- Application
 | CSig [FBind]             -- Record type
 | CEStr [CAssign]          -- Expandable record
 | CProj CExpr Field        -- Projection
 | CWld                     -- Wildcard/underscore

data CSigma = CS [(Name,CExpr)]

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
    CProj e f -> show e ++"."++ f
    CWld -> "_"

instance Show CSigma where
  show (CS ls) = show ls

instance Show FList where
  show = concatMap (brace . show) . getList
