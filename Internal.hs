module Internal where

type N = String
type F = String

newtype Substitution = Sub (Term,N)

newtype Bind = Bind (N,Term)

type Type = Term

data Assign = Expr Term | Named N Term 
data Phi = Phi Assign Type


data Term = 
   Set
 | Cns N 
 | Var N
 | Fun (N,Term) Term
 | Lam (N,Term) Term
 | App Term Term
 | Sig [Bind]
 | Struct [Assign]
 | Proj Term N 
 | ProjT Term N Term
 | Meta Meta
 | Subst Term Substitution


data Meta = M N Gamma

data Gamma = Gamma [(N,Term)]

data Xi = Xi {metaC :: Int, constraints :: [Constraint], metas :: [Meta]}


data Constraint = ExpC Term Type Term Type

{-    Empty
  | Intro Xi Meta
  | Inst Xi Meta Term
  | ExpnC Term Term Term Term
  | ProjC F Term Term
  | SubsC [F] Term
-}
