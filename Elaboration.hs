{-# LANGUAGE TupleSections #-}
{-# OPTIONS -W -Wall #-}
-- | Elaboration is the transformation of an expression in the Core grammar 
-- to a term in the Internal grammar, under the generation of constraints
-- on subterms of the output. The peculiar variable names are used to 
-- mimic the formal rules declared in the report to which this implementation
-- is related.
module Elaboration where

import DList
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
elaborate :: Sigma -> CExpr -> Type -> (Log, Either Error Term)
elaborate sig e _T = swap $ evalState (elab_ sig e _T) emptyXi

-- Elaborate - return log, final context and term
elaborate' :: Sigma -> CExpr -> Type -> (Log, Xi, Either Error Term)
elaborate' sig e _T = (eLog,xi,term)
  where ((term,eLog),xi) = runState (elab_ sig e _T) emptyXi

-- helper
elab_ :: Sigma -> CExpr -> Type -> State Xi (Either Error Term, Log)
elab_ sig e _T = runReaderT (runWriterT (runExceptT (check e _T))) (sig,Env [])


-- Environment synonyms - typed constants and variables
type TCEnv = (Sigma,Gamma)

sigma :: TCEnv -> Sigma
sigma = fst

gamma :: TCEnv -> Gamma
gamma = snd

-- Type checking monad - error handling, progress logging,
-- reader for constants and local variables, state for meta/constraint store
type TCM = ErrT (LogT (ReaderT TCEnv (State Xi)))


-- ##    Logging    ## -------------------------------------

-- Simple logging - arbitrary strings
say :: String -> TCM ()
say s = lift $ tell (toDList (s ++ "\n"))

-- Logging deferring to descriptions from a data type
sayRule :: Rule -> TCM ()
sayRule r = lift $ tell (toDList (show r ++ "\n"))


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
check :: CExpr -> Type -> TCM Term
check e _T = case (e,_T) of
  (CLam r1 fs v1 e', IFun (r2,ISig fT) (IFun (v2,_U) _V)) -> do
    say "Special lambda check"
    sg <- subSD fs fT
    let sub _1 _2 = (Sub (IVar _1) _2 ®)
        _U' = sub r1 r2 _U
        _V' = sub v1 v2 $ sub r1 r2 _V
        br = (r1,sg)
        bv = (v1,_U')
    et <- addBinds [bv,br] $ e' ⇇ _V'
    return(ILam br (ILam bv et))
  (CEStr phiS, ISig fT) -> do
    say "Special struct check"
    assn <- phiExp phiS fT
    return (IStruct assn)
  (CWld,_) -> freshMeta _T
  _ -> sayRule CheckGen >> do
    (_U,u) <- infer e
    genEq u _U _T

(⇇) :: CExpr -> Type -> TCM Term
(⇇) = check


-- Equality will either resolve immediately through reflexivity - or generate an equality constraint
-- even better would be to just check if they are wrong straight away (very much possible)
genEq :: Term -> Type -> Type -> TCM Term
genEq u _U _T | _T =$= _U = sayRule EqRedRefl >> return u
--              | _T =@= _U = say "Left meta assignment" >> addAss _T _U >> return u
--              | _U =@= _T = say "Right meta assignment" >> addAss _U _T >> return u
              | otherwise = sayRule EqRedGenC >> do
                  say $ "The types: " ++ showTerm _T ++ " and " ++ showTerm _U ++
                    " are not equal, generating equality constraint."
                  _Y <- freshMeta _T
                  addC (EquC _U _T _Y u)
                  return _Y
--  where addAss (IMeta m _) _U = addC (Assignment m _U)


--(=@=) :: Type -> Type -> Bool
--(IMeta (Meta _ _T g) []) =@= _U = _T == ISet && _U `inContext` g
--_                        =@= _  = False


-- ##  Inference rules  ## ---------------------------------

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


-- Elaborate the type of types
infSet :: TCM (Type,Term)
infSet = return (ISet,ISet)

-- Elaborate a constant
infCons :: String -> TCM (Type,Term)
infCons k = (,ICns k) <$> lookupSigma k

-- Elaborate a variable reference
infVar :: Ref -> TCM (Type,Term)
infVar x = (,IVar x) <$> lookupGamma x

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
  say "Generating subsequence constraint"
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
  (IFun (x, _U) _V) -> sayRule AppKnown >> do
    u <- e ⇇ _U
    return (IApp t u, Sub u x ® _V)
  _ -> sayRule AppUnknown >> do
    (_U,u) <- infer e
    x  <- freshBind 
    _Y <- addBind (x,_U) $ freshMeta ISet
    t' <- genEq t _T (IFun (x,_U) _Y)
    return (IApp t' u, Sub u x ® _Y)

-- Expand structs, inserting metavariables for missing arguments
-- fails if there are too many arguments (relative to expl. assignments)
phiExp :: [CAssign] -> [IBind] -> TCM [Assign']
phiExp []  [] = return []
phiExp _   [] = throwError "Too many/out-of-order arguments for expansion!"
phiExp _as (IBind f _T : bs) = go _as
  where go [] = nomatch []
        go assn@(as:ass) = case as of
            CPos e -> match e
            CNamed f' e ->
              if f == f'
              then match e
              else nomatch assn
          where match e = do
                  t <- e ⇇ _T
                  assn' <- phiExp ass bs
                  return (Ass f t : assn')
        nomatch assn = do
                t <- freshMeta _T
                assn' <- phiExp assn bs
                return (Ass f t : assn')

-- Check if the bindings are a subsequence of declarations from a sig,
-- returning the sig if it is the case
subSD :: FList -> [IBind] -> TCM Type
subSD fl fT = do
  say "Running subsequence check"
  unless (subsequence (getList fl) (map ibF fT)) $ throwError
    (show fl ++ " is not a subsequence of " ++ show fT)
  return (ISig fT)
  
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
    let substs = map (Sub proj . field ) fs'
    return (proj, foldl (flip sigmaFun) _U substs)
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


-- ##  Xi-related operations  ## ---------------------------

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


-- ##  Rule references ## ----------------------------------

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
