-- | Tying scope checking and type checking together by using checking problems
module CheckHub where

import Surface
import Core
import ScopeChecking
import Elaboration
import Internal
import Types


import Control.Arrow
import Prelude hiding (log)

-- Wrapping a type checking problem
-- the expressions of the tuple list are turned into
-- constants (in order) and have to be fully type checked
data ChkProb = ChkProb {constants :: [(N,SExpr)], term ::  SExpr, typ :: SExpr}


processProb :: ChkProb -> Either Error (Term,Xi) 
processProb prob = do
  _Σ <- makeConstants (constants prob)
  let (log1,_D') = scopecheck (typ prob)
  _D <- _D'
  let (log2,_T') = elaborate _Σ _D ISet
  _T <- _T'
  if not (isFinal _T)
  then Left $ "Type checked against must be finalized: " ++ show _T
  else do
  let (log3,e') = scopecheck (term prob)
  e <- e'
  let (log4,xi,term') = elaborate' _Σ e _T
  term <- term'
  return (term,xi)



makeConstants :: [(N,SExpr)] -> Either Error Sigma
makeConstants ls = case consts of
                    Left e -> Left e
                    Right cs -> go [] $ zip ns cs 
  where (ns,exprs) = unzip ls
        (logs,consts) = second sequence $ unzip . map scopecheck $ exprs
        go env [] = Right (Env env)
        go env ((n,e):cns) = case elaborate (Env env) e ISet of
          (log, Right t) -> if isFinal t
                            then go (env++[(n,t)]) cns
                            else Left $ "postulates must be fully solved! \n" ++ show t
          (log,Left e') -> Left e'
