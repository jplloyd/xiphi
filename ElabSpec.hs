module ElabSpec where

import Elaboration
import Types
import Internal
import Core

import Control.Monad
import Data.Maybe
import Data.List
import Control.Monad.Reader
import Control.Monad.Writer
import Control.Monad.State
import Control.Monad.Except
import Control.Arrow

-- Elaborate packaged problems (postulate-programs)

elabProblem :: [(Name,CExpr)] -> CExpr -> CExpr -> (Log, Xi, ([(Name,CExpr)], CExpr,CExpr), Either Error ([(Name,Type)],Type,Term))
elabProblem posts typ trm = (eLog,xi,(posts,typ,trm),term)
  where ctxM = flip runReaderT (Env [],Env []) . runWriterT . runExceptT $ checkProblem posts typ trm
        ((term,eLog),xi) = runState ctxM emptyXi

checkProblem :: [(Name,CExpr)] -> CExpr -> CExpr -> TCM ([(Name,Type)],Type,Term)
checkProblem posts typ trm = do
  sigm@(Env ls) <- checkPostulates posts
  say $ "## PROBLEM STEP ## : Checking that " ++ show typ  ++ " is a type"
  type' <- local (first (const sigm)) $ check typ ISet
  say "## PROBLEM STEP ## : Checking the expression against the type"
  term <- local (first (const sigm)) $ check trm type'
  return (ls,type',term)

checkPostulates :: [(Name,CExpr)] -> TCM Sigma
checkPostulates = go
  where go [] = return (Env [])
        go ((n,e):rs) = do
          say "##############################"
          say $ "Checking the postulate " ++ n
          say "##############################"
          t <- check e ISet
          t' <- instPerhaps t
          say $ "Adding " ++ n ++ " to Sigma"
          (Env ls) <- local (first (liftE ((n,t'):))) $ go rs
          return (Env $ (n,t'):ls)

instPerhaps :: Term -> TCM Term
instPerhaps t = do
  (Xi _ _ cnstr metas') <- get
  (cs,ms,t') <- resolve t cnstr metas'
  modify (replConstr cs)
  modify (replMetas ms)
  return t'

resolve :: Term -> [ContextConstraint] -> [Meta] -> TCM ([ContextConstraint],[Meta],Term)
resolve t _cs ms = case _cs of
  [] -> return ([],ms,t)
  (CConstr _ (Assignment m _T):cs) -> do
    say $ "Time to instantiate: " ++ show m ++ " with " ++ showTerm _T
    let t' = instantiate m _T t
    let ms' = delete m ms
    resolve t' cs ms'
  (c:cs) -> do
    (cs',ms',t') <- resolve t cs ms
    return (c:cs',ms',t')

-- solve all Assignment constraints

elabOptProblem :: [((Name,CExpr),Maybe Type)] -> CExpr -> (CExpr, Maybe Type) -> (Log, Xi, ([(Name,CExpr)], CExpr,CExpr), Either Error ([(Name,Type)],Type,Term))
elabOptProblem posts termC typeC = (eLog,xi,(map fst posts,fst typeC,termC),term)
  where errM = checkOptProblem posts termC typeC
        logM = runExceptT errM
        ctxM = runWriterT logM
        mtsM = runReaderT ctxM (Env [],Env [])
        ((term,eLog),xi) = runState mtsM emptyXi

checkOptPostulates :: [((Name,CExpr),Maybe Type)] -> TCM Sigma
checkOptPostulates = go
  where go [] = return (Env [])
        go (((n,e),mbt):rs) = do
          say "##############################"
          say $ "Processing the postulate " ++ n
          say "##############################"
          t <- maybe (check e ISet) return mbt
          when (isJust mbt) $ finCheck (fromJust mbt) >> say ("Type for the postulate: " ++ n ++ " was provided directly")
          say $ "Adding " ++ n ++ " to Sigma"
          (Env ls) <- local (first (liftE ((n,t):))) $ go rs
          return (Env $ (n,fromMaybe t mbt):ls)
        finCheck t = unless (isFinal t) $ throwError "Cannot provide non-finalized types manually"

checkOptProblem :: [((Name,CExpr),Maybe Type)] -> CExpr -> (CExpr, Maybe Type) -> TCM ([(Name,Type)],Type,Term)
checkOptProblem posts trm (typ,mbt) = do
  sigm@(Env ls) <- checkOptPostulates posts
  when (isNothing mbt) $ say $ "## PROBLEM STEP ## : Checking that " ++ show typ  ++ " is a type"
  when (isJust mbt) $ say ("The type has been provided directly: " ++ showTerm (fromJust mbt))
  type' <- local (first (const sigm)) $ maybe (check typ ISet) return mbt
  say "## PROBLEM STEP ## : Checking the expression against the type"
  let _T = fromMaybe type' mbt
  term <- local (first (const sigm)) $ check trm _T
  return (ls,_T,term)
