module ElabSpec where

import Derivation
import Elaboration
import Types
import Internal
import Core

import Control.Monad
import Data.Maybe
import Control.Monad.Reader
import Control.Monad.Writer
import Control.Monad.State
import Control.Monad.Except
import Control.Arrow

-- Elaborate packaged problems (postulate-programs)

elabProblem :: [(Name,CExpr)] -> CExpr -> CExpr -> ([Rule], Xi, ([(Name,CExpr)], CExpr,CExpr), Either Error ([(Name,Type)],Type,Term))
elabProblem posts typ trm = (eLog,xi,(posts,typ,trm),term)
  where ctxM = flip runReaderT (Env [],Env []) . runWriterT . runExceptT $ checkProblem posts typ trm
        ((term,eLog),(_,xi)) = runState ctxM (0,emptyXi)

checkProblem :: [(Name,CExpr)] -> CExpr -> CExpr -> TCM ([(Name,Type)],Type,Term)
checkProblem posts typ trm = do
  sigm@(Env ls) <- checkPostulates posts
  sayRule Delimiter
  type' <- local (first (const sigm)) $ check typ ISet
  sayRule Delimiter
  modify (first (const 0)) -- reset deriv counter
  term <- local (first (const sigm)) $ check trm type'
  return (ls,type',term)

checkPostulates :: [(Name,CExpr)] -> TCM Sigma
checkPostulates = go
  where go [] = return (Env [])
        go ((n,e):rs) = do
          t <- check e ISet
          sayRule Delimiter
          modify (first (const 0)) -- reset deriv counter
          (Env ls) <- local (first (liftE ((n,t):))) $ go rs
          return (Env $ (n,t):ls)
