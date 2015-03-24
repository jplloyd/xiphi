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
  term <- local (first (const sigm)) $ check trm type'
  return (ls,type',term)

checkPostulates :: [(Name,CExpr)] -> TCM Sigma
checkPostulates = go
  where go [] = return (Env [])
        go ((n,e):rs) = do
          modify (first (const 0))
          t <- check e ISet
          sayRule Delimiter
          (Env ls) <- local (first (liftE ((n,t):))) $ go rs
          return (Env $ (n,t):ls)

elabOptProblem :: [((Name,CExpr),Maybe Type)] -> CExpr -> (CExpr, Maybe Type) -> ([Rule], Xi, ([(Name,CExpr)], CExpr,CExpr), Either Error ([(Name,Type)],Type,Term))
elabOptProblem posts termC typeC = (eLog,xi,(map fst posts,fst typeC,termC),term)
  where errM = checkOptProblem posts termC typeC
        logM = runExceptT errM
        ctxM = runWriterT logM
        mtsM = runReaderT ctxM (Env [],Env [])
        ((term,eLog),(_,xi)) = runState mtsM (0,emptyXi)

checkOptPostulates :: [((Name,CExpr),Maybe Type)] -> TCM Sigma
checkOptPostulates = go
  where go [] = return (Env [])
        go (((n,e),mbt):rs) = do
          t <- maybe (check e ISet) return mbt
          when (isJust mbt) $ finCheck (fromJust mbt)
          (Env ls) <- local (first (liftE ((n,t):))) $ go rs
          return (Env $ (n,fromMaybe t mbt):ls)
        finCheck t = unless (isFinal t) $ throwError "Cannot provide non-finalized types manually"

checkOptProblem :: [((Name,CExpr),Maybe Type)] -> CExpr -> (CExpr, Maybe Type) -> TCM ([(Name,Type)],Type,Term)
checkOptProblem posts trm (typ,mbt) = do
  sigm@(Env ls) <- checkOptPostulates posts
  type' <- local (first (const sigm)) $ maybe (check typ ISet) return mbt
  let _T = fromMaybe type' mbt
  term <- local (first (const sigm)) $ check trm _T
  return (ls,_T,term)
