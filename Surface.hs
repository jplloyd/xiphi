module Surface where


import Util 

type N = String

data Bind = Bind N Expr

data Assign = Pos Expr | Named N Expr

-- Expressions in the surface language
data Expr = 
   Set 
 | Cns N 
 | Var N 
 | Fun [Bind] Bind Expr 
 | App Expr [Assign] Expr
 | Lam [N] N Expr
 | Wld

data SSigma = SS [(N,Expr)]

instance Show Expr where
  show e' = case e' of 
   Set -> "Set"
   Var n -> n
   Cns n -> "Const_" ++ n
   Fun impl expl cod -> pTele True impl ++ " " ++ pBind False expl ++ "->" ++ show cod
   App e1 impl e2 -> unwords [show e1,pAssgn impl,show e2]
   Lam impl var e -> "\\" ++ concatMap brace impl ++ " " ++ var ++ " -> " ++ show e
   Wld -> "_"

-- Print declared function telescope
pTele :: Bool -> [Bind] -> String
pTele impl = concatMap (pBind impl)


pBind :: Bool -> Bind -> String
pBind True (Bind n e) = brace $ n ++ ":" ++ show e
pBind False (Bind n e) = par $ n ++ ":" ++ show e

pAssgn :: [Assign] -> String
pAssgn = unwords  . map show


instance Show Assign where
  show e = brace $ case e of
    Pos e' -> show e'
    Named n e' -> n ++ ":=" ++ show e'  

