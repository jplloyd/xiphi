{-# LANGUAGE TupleSections #-}
{-# OPTIONS -W -Wall #-}
module Elaboration where

import DList
import Core as C
import Internal hiding (addBind,addBinds)
import qualified Internal as I
import Types
import Util

import Control.Arrow
import Control.Applicative

import Control.Monad.Except
import Control.Monad.State
import Control.Monad.Reader
import Control.Monad.Trans.Writer


-- Note that all terms are fully normalized at all stages expect during
-- the normalization stage that is substitution (internally)

-- The thing-in-itself -- takes a constant context and starts from a check on the given expression.
-- Could alt. take two exprsesion and just elab one first - alternatives can be written when needed.
elaborate :: Sigma -> CExpr -> Type -> (Log, Either Error Term)
elaborate _Σ e _T = (eLog,term)
  where errM = check e _T
        logM = runExceptT errM
        ctxM = runWriterT logM
        mtsM = runReaderT ctxM (_Σ,Env [])
        (term,eLog) = evalState mtsM emptyXi

elaborate' :: Sigma -> CExpr -> Type -> (Log, Xi, Either Error Term)
elaborate' _Σ e _T = (eLog,xi,term)
  where errM = check e _T
        logM = runExceptT errM
        ctxM = runWriterT logM
        mtsM = runReaderT ctxM (_Σ,Env [])
        ((term,eLog),xi) = runState mtsM emptyXi

elabProblem :: [(Name,CExpr)] -> CExpr -> CExpr -> (Log, Xi, ([(Name,CExpr)], CExpr,CExpr), Either Error ([(Name,Type)],Type,Term))
elabProblem posts typ trm = (eLog,xi,(posts,typ,trm),term)
  where errM = checkProblem posts typ trm
        logM = runExceptT errM
        ctxM = runWriterT logM
        mtsM = runReaderT ctxM (Env [],Env [])
        ((term,eLog),xi) = runState mtsM emptyXi

checkPostulates :: [(Name,CExpr)] -> TCM Sigma
checkPostulates = go
  where go [] = return (Env [])
        go ((n,e):rs) = do
          say "##############################"
          say $ "Checking the postulate " ++ n
          say "##############################"
          t <- check e ISet
          say $ "Adding " ++ n ++ " to Sigma"
          (Env ls) <- local (first (liftE ((n,t):))) $ go rs
          return (Env $ (n,t):ls)

checkProblem :: [(Name,CExpr)] -> CExpr -> CExpr -> TCM ([(Name,Type)],Type,Term)
checkProblem posts typ trm = do
  sigm@(Env ls) <- checkPostulates posts
  say $ "## PROBLEM STEP ## : Checking that " ++ show typ  ++ " is a type"
  type' <- local (first (const sigm)) $ check typ ISet
  say "## PROBLEM STEP ## : Checking the expression against the type"
  term <- local (first (const sigm)) $ check trm type'
  return (ls,type',term)


-- Environment synonyms - typed constants and variables
type TCEnv = (Sigma,Gamma)

sigma :: TCEnv -> Sigma
sigma = fst

gamma :: TCEnv -> Gamma
gamma = snd

-- Type checking monad -
-- error handling,
-- progress logging,
-- reader for constants and local variables,
-- state for meta/constraint store
type TCM = ErrT (LogT (ReaderT TCEnv (State Xi)))


-- ##    Logging    ##

-- Simple logging - arbitrary strings
say :: String -> TCM ()
say s = lift $ tell (toDList (s ++ "\n"))

-- Logging deferring to descriptions from a data type
sayRule :: Rule -> TCM ()
sayRule r = lift $ tell (toDList (show r ++ "\n"))


-- ##  Context functions  ##

-- Add a binding to Gamma
addBind :: (Ref,Type) -> TCM a -> TCM a
addBind b = local (second (I.addBind b))

-- Add multiple bindings to Gamma
addBinds :: [(Ref,Type)] -> TCM a -> TCM a
addBinds bs = local (second (I.addBinds bs))

-- Look up the type of a constant
lookupSigma :: String -> TCM Type
lookupSigma n = lookupE n . sigma <$> ask >>= \mt -> maybeErr mt id errMsg
    where errMsg = "Constant reference" ++ show n ++ " not in scope!"

-- Look up the type of a variable
lookupGamma :: Ref -> TCM Type
lookupGamma n = lookupE n . gamma <$> ask >>= \mt -> maybeErr mt id errMsg
    where errMsg = "Variable reference" ++ show n ++ " not in scope!"


-- ##  Checking and equality  ##

-- Check a core expression against a type
check :: CExpr -> Type -> TCM Term
check e _T = sayRule CheckGen >> do
  (_U,u) <- infer e
  genEq u _U _T

(⇇) :: CExpr -> Type -> TCM Term
(⇇) = check

-- Equality will either resolve immediately through reflexivity - or generate an equality constraint
-- even better would be to just check if they are wrong straight away (very much possible)
genEq :: Term -> Type -> Type -> TCM Term
genEq u _U _T | _T == _U = sayRule EqRedRefl >> return u
              | otherwise = sayRule EqRedGenC >> do
                  _Y <- freshMeta _T
                  addC (EquC _U _T _Y u)
                  return _Y

-- ##  Inference rules  ##

 -- ElabM will now have a reader for constants and possibly for Gamma as well
infer :: CExpr -> TCM (Type,Term)
infer _e = case _e of
  CCns n       -> sayRule InferCns >> infCons n
  CVar r       -> sayRule InferVar >> infVar r
  CSet         -> sayRule InferSet >> infSet
  CFun b e     -> sayRule InferFun >> infFun b e
  CLam r i e b -> sayRule InferLam >> infLam r i e b
  CApp e1 e2   -> sayRule InferApp >> infApp e1 e2
  CSig bsd     -> infSig bsd
  CEStr n      -> sayRule InferEStr >> infEStr n
  CProj e f    -> sayRule InferProj >> infProj e f
  CWld         -> sayRule InferWld >> infWld

-- Elaborate a constant
infCons :: String -> TCM (Type,Term)
infCons k = (,ICns k) <$> lookupSigma k

-- Elaborate a variable reference
infVar :: Ref -> TCM (Type,Term)
infVar x = (,IVar x) <$> lookupGamma x

-- Elaborate the type of types
infSet :: TCM (Type,Term)
infSet = return (ISet,ISet)

-- Elaborate function types
infFun :: CBind -> CExpr -> TCM (Type,Term)
infFun (CBind x _D) _E = do
  _U <-                  _D ⇇ ISet
  _V <- addBind (x,_U) $ _E ⇇ ISet
  return (ISet,IFun (x,_U) _V)

-- Elaborate an expandable Lambda
infLam :: Ref -> FList -> Ref -> CExpr -> TCM (Type,Term)
infLam r fv x e = do
  _T <- subS fv
  _U <- addBind (r,_T) $ freshMeta ISet
  (_V,v) <- addBinds [(r,_T),(x,_U)] $ infer e
  return (IFun (r, _T) (IFun (x,_U) _V), ILam (r,_T) (ILam (x,_U) v))

-- f ⊆ T - special subsequence constraint things
subS :: FList -> TCM Type
subS fl = do
  _X <- freshMeta ISet
  say "Generating subsequence constraint"
  addC (SubC _X (getList fl))
  return _X

-- Elaborate an application
infApp :: CExpr -> CExpr -> TCM (Type,Term)
infApp e1 e2 = do
  (_T,t) <- infer e1
  (_U,u) <- infer e2
  (v,_V) <- appAt (t,_T) (u,_U)
  return (_V,v)

-- (t : T)@(u : U) ~> v
-- If the thing is a known function type - run the equality thingy right away
appAt :: (Term,Type) -> (Term,Type) -> TCM (Term,Type)
appAt (t, IFun (x, _U') _V) (u, _U) = sayRule AppKnown >> do
  u' <- genEq u _U _U'
  return (IApp t u', subst [Sub u' x] _V) -- a point of substitution
appAt (t,_T) (u,_U) = sayRule AppUnknown >> do
  x  <- freshBind 
  _Y <- addBind (x,_U) $ freshMeta ISet
  t' <- genEq t _T (IFun (x,_U) _Y)
  return (IApp t' u, subst [Sub u x] _Y) -- subst can ofc be bypassed here
  
-- Elaborate a record type
-- This elaboration is very tedious when following the rules exactly
infSig :: [FBind] -> TCM (Type,Term)
infSig fs = case fs of 
  [] -> sayRule InferRecB >> return (ISet, ISig [])
  (FBind f _D : fs') -> sayRule InferRecC >> do
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
genExp phis = say "Generating expansion constraint" >> do
  (_Y,_X) <- freshMetas
  addC (ExpC _X phis _Y)
  return (_X,_Y)

-- Special elaboration of assignments
phiInf :: CAssign -> TCM Phi
phiInf phiC = say "Invoking special phi inference" >> do
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
    say "Transforming projection type"
    (fs',_U) <- sigLookup fs f
    let proj = IProj t f
    return (proj,subst (map (Sub proj . field) fs') _U) -- even more substitutions
  _          -> do
    say "Generating projection constraint"
    (_Y,_X) <- freshMetas
    addC (PrjC _T t f _Y _X)
    return (_Y,_X)
  
-- Elaborate an unknown expression
infWld :: TCM (Type,Term)
infWld = do -- swap <$> freshMetas
  (_Y,_X) <- freshMetas
  return (_X,_Y)


-- ##  Xi-related operations  ##

-- Generate a fresh metavariable of a given type
freshMeta :: Type -> TCM Term
freshMeta _T = sayRule FreshMeta >> do
  metaIdx <- metaC <$> get
  modify incMetaC
  _Γ <- gamma <$> ask 
  let meta = Meta metaIdx _T _Γ
  modify (addMeta meta)
  return $ IMeta meta []

-- Generate two fresh metavariables,
-- the second being the type of the first
freshMetas :: TCM (Term,Type)
freshMetas = sayRule FreshMetas >> do
  _X <- freshMeta ISet
  _Y <- freshMeta _X
  return (_Y,_X)

-- Guaranteed fresh bind (unknown binds are not created during scope checking)
freshBind :: TCM Ref
freshBind = say "Creating a fresh binding" >> do
  bC <- bindC <$> get
  modify incBindC
  return $ V Unknown bC

-- Add a constraint with current context to constraint store
addC :: Constraint -> TCM ()
addC _C = sayRule AddConstraint >> do
  _Γ <- gamma <$> ask -- retrieve the current variable context
  say $ "Creating a constraint with this context: " ++ show _Γ
  modify (addConstraint (CConstr _Γ _C)) -- add the constraint to the store


-- ##  Rule references ##

-- Rules used in type checking - show instance will reference rules (eventually)
data Rule =
   CheckGen -- Check/Eq stuff <
 | EqRedRefl --               <
 | EqRedGenC --               <
-- ============================
 | InferSet -- Basics < 
 | InferCns --        <
 | InferVar --        <
 | InferWld --        <
 | InferFun --        <
 | InferRecB --       <
 | InferRecC --       <
-- ====================
 | InferApp -- Applications <
 | AppKnown --              <
 | AppUnknown --            <
-- ==========================
 | InferLam -- Lambdas      <
 | SubSeqGenC --            <
-- ==========================
 | InferEStr -- Exp. Struct <
 | InferPhiS --             <
 | ExpGenC --               <
-- ==========================
 | InferProj -- Projections <
 | ProjRed --               <
 | ProjGenC --              <
-- ==========================
 | FreshMeta -- Xi Operations <
 | FreshMetas --              <
 | AddConstraint --           <
-- ============================
  deriving Show


-- Substitution/Reduction -- The work of Eskil M Johànsen Esq.

type Ss = [Substitution]

-- ComputeSubst: Should always return a reduced term
subst :: Ss -> Term -> Term
subst ss = reduce . sp ss

-- SubstProp: May return an unreduced term.
-- Doesn't this feel like a functor operation? Ah well...
sp :: Ss -> Term -> Term
sp ss trm = case trm of
  (IVar x)       -> sigma' ss x
  (IFun (r,u) v) -> IFun (r,sp' u) (sp' v)
  (ILam (r,u) v) -> ILam (r,sp' u) (sp' v)
  (IApp t1 t2)   -> IApp (sp' t1) (sp' t2)
  (ISig ibs)     -> ISig    $ map intoBindings ibs
  (IStruct ass)  -> IStruct $ map intoAssignss ass
  (IProj t f)    -> IProj (sp' t) f
  (IMeta x olds) -> IMeta x (composeSubsts olds ss)
  _ -> trm -- Set and constants
 where sp' = sp ss
       intoBindings (IBind n t) = IBind n $ sp' t
       intoAssignss (Ass   n t) = Ass   n $ sp' t

-- SigmaFun: Computes actual substitution on a variable
sigma' :: Ss -> Ref -> Term
sigma' ss x = case ss of
  [] -> IVar x
  (Sub t y : ss') -> if y == x then t else sigma' ss' x
        
-- Beware, front of the subst list is to the left! (Other way around in report.)
composeSubsts :: Ss -> Ss -> Ss
composeSubsts olds news = foldr lars news olds
  where lars (Sub t n) = (Sub (subst news t) n :)

-- Reduces a term using rules for projections and... Nothing more?
reduce :: Term -> Term
reduce t = case t of
      (IProj (IStruct ass) f) -> reduce $ structLookup' ass f
      _ -> t

-- point of hard failure, tough
structLookup' :: [Assign'] -> Field -> Term
structLookup' as f = go as
  where go [] = error $ "Attempted projection on nonexistent field: " ++ show f
        go (Ass f' t:as') = if f' == f then t else go as'


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
