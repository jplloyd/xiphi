{-# LANGUAGE TupleSections #-}
{-# OPTIONS -Wall #-}
-- | Elaboration is the transformation of an expression in the Core grammar 
-- to a term in the Internal grammar, under the generation of constraints
-- on subterms of the output. The peculiar variable names are used to 
-- mimic the formal rules declared in the report to which this implementation
-- is related.
module Elaboration where

import Core as C
import Internal hiding (addBind,addBinds)
import qualified Internal as I
import Types
import Util
import Derivation

import Data.Tuple
import Control.Arrow
import Control.Applicative

import Control.Monad.Except
import Control.Monad.State
import Control.Monad.Reader
import Control.Monad.Trans.Writer


-- Note that all terms are fully normalized at all stages expect during
-- the normalization stage that is substitution (internally)

-- Elaborate - return log and term
elaborate :: Sigma -> CExpr -> Type -> ([Rule], Either Error Term)
elaborate sig e _T = swap $ evalState (elab_ sig e _T) (0,emptyXi)

-- Elaborate - return log, final context and term
elaborate' :: Sigma -> CExpr -> Type -> ([Rule], Xi, Either Error Term)
elaborate' sig e _T = (eLog,xi,term)
  where ((term,eLog),(_,xi)) = runState (elab_ sig e _T) (0,emptyXi)

-- helper
elab_ :: Sigma -> CExpr -> Type -> State (Int,Xi) (Either Error Term, [Rule])
elab_ sig e _T = runReaderT (runWriterT (runExceptT (check e _T))) (sig,Env [])


-- Environment synonyms - typed constants and variables
type TCEnv = (Sigma,Gamma)

sigma :: TCEnv -> Sigma
sigma = fst

gamma :: TCEnv -> Gamma
gamma = snd

-- Type checking monad - error handling, progress logging,
-- reader for constants and local variables, state for meta/constraint 
-- store and rule index (used to connect start and end in linear 
-- derivation printing + possible used for indentation)
type TCM = ErrT (WriterT [Rule] (ReaderT TCEnv (State (RuleIdx,Xi))))

-- ##    Logging    ## -------------------------------------

sayRule :: Rule -> TCM ()
sayRule r = lift (tell [r])

sayRule' :: (RuleIdx -> Rule) -> TCM RuleIdx
sayRule' f = do
  idx <- fst <$> get
  modify $ first (+1)
  sayRule (f idx)
  return idx

-- ##  Context functions  ## -------------------------------

-- Add a binding to Gamma
addBind :: (Ref,Type) -> TCM a -> TCM a
addBind b = local (second (I.addBind b))

-- Add multiple bindings to Gamma
addBinds :: [(Ref,Type)] -> TCM a -> TCM a
addBinds bs = local (second (I.addBinds bs))

-- Look up the type of a constant
lookupSigma :: String -> TCM Type
lookupSigma n = lookupE n . sigma <$> ask >>= \mt -> maybeErr mt id errMsg
    where errMsg = "Constant reference: " ++ show n ++ " is not in scope!"

-- Look up the type of a variable
lookupGamma :: Ref -> TCM Type
lookupGamma n = lookupE n . gamma <$> ask >>= \mt -> maybeErr mt id errMsg
    where errMsg = "Variable reference: " ++ showRef n ++ " is not in scope!"


-- ##  Checking and equality  ## ---------------------------

-- Check a core expression against a type
(⇇) :: CExpr -> Type -> TCM Term
(⇇) = check

check :: CExpr -> Type -> TCM Term
check _e _T = case (_e,_T) of
    (CLam (CBind x1 _D) e, IFun (x2,_U) _V) -> do
      ridx <- sayRule' (chkInd _e _T CheckLam) -- LOG
      lamTChk _D _U
      let bx = (x1,_U)
          _V' = Sub (IVar x1) x2 ® _V
      sayRule (Simple GenSubst) -- LOG
      v <- addBinds [bx] $ e ⇇ _V'
      let t = ILam bx v
      sayRule (chkRes t ridx) -- LOG
      return t
    (CLam _ _, _) -> genChkConstraint _e _T
    (CEStr phiCs, ISig fUs) -> do
      let rule = if null phiCs then CheckExpB else CheckExpC
      ridx <- sayRule' (chkInd _e _T rule) -- LOG
      t <- liftM IStruct $ expRec phiCs fUs
      sayRule (chkRes t ridx) -- LOG
      return t
    (CEStr _, _) -> genChkConstraint _e _T
    (CWld,_) -> do
      t <- freshMeta _T
      sayRule (chkCmp _e _T CheckWld [FreshMeta] t) -- LOG
      return t
    _ -> do
      ridx <- sayRule' (chkInd _e _T CheckGen) -- LOG
      (_U,u) <- infer _e
      t <- chkEq u _U _T
      sayRule (chkRes t ridx) -- LOG
      return t
  where 
    lamTChk :: CExpr -> Type -> TCM ()
    lamTChk CWld       _          = return ()
    lamTChk (CESig fs) (ISig fUs) =
        unless (subsequence (getList fs) (map ibF fUs)) $ throwError
          (show fs ++ " is not a subsequence of " ++ show fUs)
    lamTChk _          _          = throwError "No support for bound type"

genChkConstraint :: CExpr -> Type -> TCM Term
genChkConstraint _e _T = do
      _X <- freshMeta _T
      sayRule (infCmp _e InferESig [FreshMeta,SubSeqGenC] ISet _X) -- LOG
      addC (ChkC _e _T _X)
      return _X

-- Expand structs, inserting metavariables for missing arguments
-- fails if there are too many arguments (relative to expl. assignments)
expRec :: [CAssign] -> [IBind] -> TCM [Assign']
expRec phiCs fUs = case (phiCs,fUs) of
    ([], []) -> return [] -- Base
    (_ , []) -> throwError 
      "Too many/out-of-order arguments for expansion!"
    (_, (IBind f _U) : fUs') -> do  -- Cons
      let (tcm_u, phiCs') = phiFun f _U
      u <- tcm_u
      fus <- expRec phiCs' $ substBinds (Sub u $ field f) fUs'
      return (Ass f u : fus)
  where phiFun f _U = case phiCs of
            ((CPos      e) : asss)           -> (e ⇇ _U, asss) -- Match
            ((CNamed f' e) : asss) | f' == f -> (e ⇇ _U, asss) -- Match
            _ -> (freshMeta _U, phiCs) -- No match


-- Equality will either resolve immediately through alpha conversion and reflexivity,
-- or it will generate an equality constraint.
-- Even better would be to just check if they are wrong straight away (very much possible).
chkEq :: Term -> Type -> Type -> TCM Term
chkEq u _U _T | _T =$= _U = sayRule (Simple EqRedRefl) {- LOG -} >> return u
              | otherwise = do -- Generate equality constraint 
                  sayRule (Simple EqRedGenC)
                  _X <- freshMeta _T
                  addC (EquC u _U _T _X)
                  return _X

-- ##  Inference rules  ## ---------------------------------

 -- ElabM will now have a reader for constants and possibly for Gamma as well
infer :: CExpr -> TCM (Type,Term)
infer _e = case _e of
  CSet       -> infSet
  CCns n     -> infCons n
  CVar r     -> infVar r
  CFun b e   -> infFun b e
  CApp e1 e2 -> infApp e1 e2
  CSig bsd   -> infSig bsd
  CProj e f  -> infProj e f
  _          -> error $ "No inference rule exists for core expression: "
                          ++ show _e 

-- Elaborate the type of types
infSet :: TCM (Type,Term)
infSet = sayRule (Simple InferSet) {- LOG -} >> return (ISet,ISet)

-- Elaborate a constant
infCons :: String -> TCM (Type,Term)
infCons k = do
  _T <- lookupSigma k
  let t = ICns k
  sayRule (infCmp (CCns k) InferCns [] _T t) -- LOG
  return (_T,t)

-- Elaborate a variable reference
infVar :: Ref -> TCM (Type,Term)
infVar x = do
  _T <- lookupGamma x
  let t = IVar x
  sayRule (infCmp (CVar x) InferVar [] _T t) -- LOG
  return (_T,t)

-- Elaborate function types
infFun :: CBind -> CExpr -> TCM (Type,Term)
infFun cb@(CBind x _D) _E = do
  ridx <- sayRule' (infInd (CFun cb _E) InferFun) -- LOG
  _U <- _D ⇇ ISet
  _V <- addBind (x,_U) $ _E ⇇ ISet
  let t = IFun (x,_U) _V
  sayRule (infRes ISet t ridx) -- LOG
  return (ISet,t)

-- Elaborate an application
infApp :: CExpr -> CExpr -> TCM (Type,Term)
infApp e1 e2 = do
    _ <- sayRule' (infInd (CApp e1 e2) InferApp) -- LOG
    (_T, t) <- infer e1
    (x, _U, _V) <- getFunShape _T t
    sayRule (Simple AppKnown) -- LOG
    u <- e2 ⇇ _U
    return (Sub u x ® _V, IApp t u)
  where getFunShape (IFun (x, _U) _V) _ = return (x, _U, _V)
        getFunShape _T t = throwError $ unlines 
                             ["The type: " ++ show _T
                             ,"of application head: " ++ show t
                             ,"does not have a function type."
                             ]

-- Elaborate a record type
-- This elaboration is very tedious when following the rules exactly
infSig :: [FBind] -> TCM (Type,Term)
infSig fs = case fs of 
  [] -> do
    sayRule (infCmp (CSig []) InferSigB [] ISet (ISig [])) -- LOG
    return (ISet, ISig [])
  (FBind f _D : fs') -> do
    ridx <- sayRule' (infInd (CSig fs) InferSigC) -- LOG
    _U <-                                      _D ⇇ ISet
    (ISig fbs) <- addBind (field f,_U) $ CSig fs' ⇇ ISet
    let t = ISig $ IBind f _U : fbs
    sayRule (infRes ISet t ridx) -- LOG
    return (ISet, t)

-- Elaborate a projection
infProj :: CExpr -> Field -> TCM (Type,Term)
infProj e f = do
    _ <- sayRule' (infInd (CProj e f) InferProj) -- LOG
    (_T,t) <- infer e
    fs <- getSigShape _T t
    sayRule (Simple ProjRed) -- LOG
    (fs',_U) <- sigLookup fs f
    let proj = IProj t f
        substs = map (Sub proj . field ) fs'
    return (foldl (flip sigmaFun) _U substs, proj)
  where getSigShape (ISig fs) _ = return fs
        getSigShape _T t = throwError $ unlines 
                             ["The type: " ++ show _T
                             ,"of projection target: " ++ show t
                             ,"does not have a record type."
                             ]

-- ##  Xi-related operations  ## ---------------------------

-- Generate a fresh metavariable of a given type
freshMeta :: Type -> TCM Term
freshMeta _T = do
--  sayRule (Simple FreshMeta) -- LOG
  metaIdx <- metaC . snd <$> get
  modify (second incMetaC)
  _Γ <- gamma <$> ask
  let meta = Meta metaIdx _T _Γ
  modify (second (addMeta meta))
  return $ IMeta meta []

-- Guaranteed fresh bind (unknown binds are not created during scope checking)
freshBind :: TCM Ref
freshBind = do
  bC <- bindC . snd <$> get
  modify (second incBindC)
  return $ V Unknown bC

-- Add a constraint with current context to constraint store
addC :: Constraint -> TCM ()
addC _C = do
  _Γ <- gamma <$> ask -- retrieve the current variable context
  modify (second $ addConstraint (CConstr _Γ _C)) -- add the constraint to the store

-- Look up the field in a given list of binds, returning the type and preceding fields
sigLookup :: [IBind] -> Field -> TCM ([Field],Type)
sigLookup bs f = go [] bs
  where go _ [] = throwError $ "Attempted type lookup for nonexistent field: " ++ show f
        go prec (IBind f' _T : bs') = if f' == f then return (prec,_T) else go (f':prec) bs'

-- Look up the assignment to the given field, throwing an error if it is not found
structLookup :: [Assign'] -> Field -> TCM Term
structLookup as f = go as
  where go [] = throwError $ "Attempted projection on nonexistent field: " ++ show f
        go (Ass f' t:as') = if f' == f then return t else go as'
