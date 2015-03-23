{-# LANGUAGE TupleSections #-}
{-# OPTIONS -W -Wall #-}
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

type RuleIdx = Int

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
  (CLam r1 fs x1 e, IFun (r2,sig@(ISig fT)) (IFun (x2,_U) _V)) -> do
    unless (subsequence (getList fs) (map ibF fT)) $ throwError
      (show fs ++ " is not a subsequence of " ++ show fT)
    let sub _1 _2 = (Sub (IVar _1) _2 ®)
        _U' = sub r1 r2 _U
        _V' = sub x1 x2 $ sub r1 r2 _V
        br = (r1,sig)
        bx = (x1,_U')
    v <- addBinds [bx,br] $ e ⇇ _V'
    return(ILam br (ILam bx v))
  (CEStr phiCs, ISig fUs) -> do
    liftM IStruct $ expRec phiCs fUs
  (CWld,_) -> freshMeta _T
  _ -> do
    (_U,u) <- infer _e
    genEq u _U _T


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


-- Equality will either resolve immediately through reflexivity - or generate an equality constraint
-- even better would be to just check if they are wrong straight away (very much possible)
genEq :: Term -> Type -> Type -> TCM Term
genEq u _U _T | _T =$= _U = return u
              | otherwise = do
                  _Y <- freshMeta _T
                  addC (EquC _U _T _Y u)
                  return _Y

-- ##  Inference rules  ## ---------------------------------

 -- ElabM will now have a reader for constants and possibly for Gamma as well
infer :: CExpr -> TCM (Type,Term)
infer _e = case _e of
  CCns n       -> infCons n
  CVar r       -> infVar r
  CSet         -> infSet
  CFun b e     -> infFun b e
  CLam r i e b -> infLam r i e b
  CApp e1 e2   -> infApp e1 e2
  CSig bsd     -> infSig bsd
  CEStr n      -> infEStr n
  CProj e f    -> infProj e f
  CWld         -> infWld


-- Elaborate the type of types
infSet :: TCM (Type,Term)
infSet = return (ISet,ISet)

-- Elaborate a constant
infCons :: String -> TCM (Type,Term)
infCons k = do
  _T <- lookupSigma k
  let t = ICns k
  return (_T,t)

-- Elaborate a variable reference
infVar :: Ref -> TCM (Type,Term)
infVar x = do
  _T <- lookupGamma x
  let t = IVar x
  return (_T,t)

-- Elaborate function types
infFun :: CBind -> CExpr -> TCM (Type,Term)
infFun (CBind x _D) _E = do
  _U <- _D ⇇ ISet
  _V <- addBind (x,_U) $ _E ⇇ ISet
  return (ISet,IFun (x,_U) _V)

-- Elaborate an expandable Lambda
infLam :: Ref -> FList -> Ref -> CExpr -> TCM (Type,Term)
infLam r fv x e = do
  _T <- subSC fv
  let br = (r,_T)
  _U <- addBind br $ freshMeta ISet
  let bv = (x,_U)
  (_V,v) <- addBinds [bv, br] $ infer e
  return (IFun br (IFun bv _V), ILam br (ILam bv v))

-- f ⊆ T - subsequence constraint with a fresh meta for the type
subSC :: FList -> TCM Type
subSC fl = do
  _X <- freshMeta ISet
  addC (SubC _X (getList fl))
  return _X

-- Elaborate an application
infApp :: CExpr -> CExpr -> TCM (Type,Term)
infApp e1 e2 = do
  (_T,t) <- infer e1
  (v,_V) <- appAt (t,_T) e2
  return (_V,v)

-- (t : T)@e ~> (v : V)
-- If the thing is a known function type - check against domain
appAt :: (Term,Type) -> CExpr -> TCM (Term,Type)
appAt (t, _T) e = case _T of
  (IFun (x, _U) _V) -> do
    u <- e ⇇ _U
    return (IApp t u, Sub u x ® _V)
  _ -> do
    (_U,u) <- infer e
    x  <- freshBind 
    _Y <- addBind (x,_U) $ freshMeta ISet
    t' <- genEq t _T (IFun (x,_U) _Y)
    return (IApp t' u, Sub u x ® _Y)

-- Elaborate a record type
-- This elaboration is very tedious when following the rules exactly
infSig :: [FBind] -> TCM (Type,Term)
infSig fs = case fs of 
  [] -> return (ISet, ISig [])
  (FBind f _D : fs') -> do
    _U <-                                      _D ⇇ ISet
    (ISig fbs) <- addBind (field f,_U) $ CSig fs' ⇇ ISet
    return (ISet, ISig $ IBind f _U : fbs)

-- Elaborate an expandable struct
infEStr :: [CAssign] -> TCM (Type,Term)
infEStr phiCs = do
  phiIs <- mapM phiInf phiCs
  genExp phiIs
  
-- Generate expansion constraints
genExp :: [Phi] -> TCM (Type,Term)
genExp phis = do
  (_Y,_X) <- freshMetas
  addC (ExpC _X phis _Y)
  return (_X,_Y)

-- Special elaboration of assignments
phiInf :: CAssign -> TCM Phi
phiInf phiC = do
    (_V,_v) <- infer (getAExpr phiC)
    return . flip Phi _V . maybe (Pos _v) (flip Named _v) $ getAField phiC

-- Elaborate a projection
infProj :: CExpr -> Field -> TCM (Type,Term)
infProj e f = do
  (_T,t) <- infer e
  (v, _V) <- handleProj t f _T
  return (_V,v)

-- Either gnerate a projection constraint or handle the transformation directly
handleProj :: Term -> Field -> Type -> TCM (Term,Type)
handleProj t f _T = case _T of
  (ISig fs ) -> do
    (fs',_U) <- sigLookup fs f
    let proj = IProj t f
    let substs = map (Sub proj . field ) fs'
    return (proj, foldl (flip sigmaFun) _U substs)
  _          -> do
    (_Y,_X) <- freshMetas
    addC (PrjC _T t f _Y _X)
    return (_Y,_X)
  
-- Elaborate an unknown expression
infWld :: TCM (Type,Term)
infWld = do
  (_Y,_X) <- freshMetas
  return (_X,_Y)


-- ##  Xi-related operations  ## ---------------------------

-- Generate a fresh metavariable of a given type
freshMeta :: Type -> TCM Term
freshMeta _T = do
  metaIdx <- metaC . snd <$> get
  modify (second incMetaC)
  _Γ <- gamma <$> ask 
  let meta = Meta metaIdx _T _Γ
  modify (second (addMeta meta))
  return $ IMeta meta []

-- Generate two fresh metavariables,
-- the second being the type of the first
freshMetas :: TCM (Term,Type)
freshMetas = do
  _X <- freshMeta ISet
  _Y <- freshMeta _X
  return (_Y,_X)

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


-- ##  Rule references ## ----------------------------------

-- Temporary structure - still working on this
data Rule = Indexed Rule' RuleIdx
          | Unindexed Rule'
          | Simple Rule'
          | InferRes Type Term RuleIdx
          | CheckRes Term RuleIdx

data RuleType = Infer | Check

-- Rules used in type checking - show instance will reference rules (eventually)
data Rule' =
   CheckGen -- eq:checkrule
 | EqRedRefl -- eq:algeqrefl
 | EqRedGenC -- eq:addceq
-- ============================
 | InferSet -- eq:infset
 | InferCns -- eq:infc
 | InferVar -- eq:infv
 | InferWld -- eq:infunderscore
 | InferFun -- eq:inffuntyp
 | InferRecB -- eq:infrectypbas
 | InferRecC -- eq:infrectyprec
-- ====================
 | InferApp -- eq:infapp
 | AppKnown -- eq:appknown
 | AppUnknown -- eq:appunknown
-- ==========================
 | InferLam -- eq:infexplambda
 | SubSeqGenC -- eq:xiopssubs
-- ==========================
 | InferEStr -- eq:infexprec
 | InferPhiS -- eq:infphi
 | ExpGenC -- eq:xiopsstexp
-- ==========================
 | InferProj -- eq:infproj
 | ProjRed -- eq:unifprojconstraint
 | ProjGenC -- eq:xiopsproj
-- ==========================
 | FreshMeta -- Xi Operations <
 | FreshMetas --              <
 | AddConstraint --           <
-- ============================
  deriving Show


-- monadic versions, but these errors will only appear if programming in Core directly
-- (no longer the work of the gentleman mentioned above).
        
sigLookup :: [IBind] -> Field -> TCM ([Field],Type)
sigLookup bs f = go [] bs
  where go _ [] = throwError $ "Attempted type lookup for nonexistent field: " ++ show f
        go prec (IBind f' _T : bs') = if f' == f then return (prec,_T) else go (f':prec) bs'

structLookup :: [Assign'] -> Field -> TCM Term
structLookup as f = go as
  where go [] = throwError $ "Attempted projection on nonexistent field: " ++ show f
        go (Ass f' t:as') = if f' == f then return t else go as'
