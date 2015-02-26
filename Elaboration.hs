{-# LANGUAGE TupleSections #-}
{-# OPTIONS -W -Wall #-}
module Elaboration where

import Core

import Control.Monad.State
import Control.Monad.Reader

import Internal(
  Xi(..),
  Gamma(..),
  Term,
  Meta(..),
  Constraint(..),
  Substitution(..),
  Phi(..),
  emptyXi,
  addConstraint,
  incMetaC,
  addMeta,
  lookupG,
  addBind,
  incBindC,
  liftG)

import qualified Internal as I

type Type = Term
type Constants = Gamma

type ElabM = ReaderT Constants ElabM'
type ElabM' = State Xi

elaborate :: Xi -> Constants -> Expr -> Type -> Term
elaborate x c e t = flip evalState x . flip runReaderT c $ check (Gamma []) e t

elaborate' :: Constants -> Expr -> Type -> Term
elaborate' = elaborate emptyXi

check :: Gamma -> Expr -> Type -> ElabM Term
check g e t = do
  (typ,term) <- infer g e
  genEq g term typ t

infer :: Gamma -> Expr -> ElabM (Type, Term)
infer g _e = case _e of
  Set -> return (I.Set,I.Set)
  Var n -> return (lookupG g n, I.Var n)
  Cns n -> do
    c <- ask
    return (lookupG c n,I.Cns n)
  Lam (Bind n e) e' -> do
    term <- check g e I.Set
    (cod,body) <- infer (addBind (n,term) g) e'
    return (I.Fun (n, term) cod, I.Lam (n,term) body)
  Fun (Bind n e) e' -> do
    term <- check g e I.Set
    cod <- check (addBind (n,term) g) e' I.Set
    return (I.Set, I.Fun (n, term) cod)
  App e1 e2 -> do
    f@(I.Fun b@(x, dom) cod) <- getFunShape g
    t1 <- check g e1 f
    t2 <- check (addBind b g) e2 dom 
    return (I.Subst cod (Sub t2 x), I.App t1 t2)
  Sig bs -> inferSig g bs >>= \t -> return (I.Set,t)
  LSig fs -> do
    x <- genSubC g fs
    return (I.Set, x)
  EStr ass -> do
    phis <- infPhi g ass
    (t,_T) <- genExpC g phis
    return (_T,t)
  Proj e f -> do
    (typ,term) <- infer g e
    (u,uT) <- genProjC g term typ f
    return (uT,u)
  WCrd -> do
    (y,x) <- freshMetas g
    return (x,y)

inferSig :: Gamma -> [Bind] -> ElabM Term
inferSig g _bs = case _bs of 
  [] -> return $ I.Sig []
  (Bind n e : bs) -> do
    t <- check g e I.Set
    (I.Sig bs') <- inferSig (addBind (n,t) g) bs
    return $ I.Sig (I.Bind n t : bs')

infPhi :: Gamma -> [Assign] -> ElabM [Phi]
infPhi g = mapM go
  where 
    go (Pos e) = infer g e >>= \(_T,t) -> return $ Phi (I.Pos t) _T
    go (Named f e) = infer g e >>= \(_T,t) -> return $ Phi (I.Named f t) _T

genEq :: Gamma -> Term -> Type -> Type -> ElabM Term
genEq g trm typ typ' = 
  if (typ,typ') == (I.Set,I.Set)
  then return trm
  else do
    m <- freshMeta g typ'
    addConstr (EquC g m typ' trm typ)
    return m
  
-- Operations on Xi

freshMeta :: Gamma -> Type -> ElabM Term
freshMeta g t = I.MetaTerm `fmap` newMeta g t

freshMetas :: Gamma -> ElabM (Term, Type)
freshMetas g = do
  x <- freshMeta g I.Set
  y <- freshMeta g x
  return (y,x)

newMeta :: Gamma -> Type -> ElabM Meta
newMeta g t = do
  xi <- get
  let n = metaC xi
  let nMeta = Meta ("_" ++ show n) t g
  modify incMetaC
  modify (addMeta nMeta)
  return nMeta

addConstr :: Constraint -> ElabM ()
addConstr c = modify (addConstraint c)

getFunShape :: Gamma -> ElabM Type
getFunShape g = do
  dom <- freshMeta g I.Set
  x <- freshBind
  cod <- freshMeta (addBind (x,dom) g) I.Set
  return $ I.Fun (x,dom) cod

freshBind :: ElabM N
freshBind = do
  xi <- get
  let b = "_x" ++ show (bindC xi)
  modify incBindC
  return b

genProjC :: Gamma -> Term -> Type -> F -> ElabM (Term,Type)
genProjC g term typ f = 
  if sig typ then do
    let substs = getSubsts f term typ
    let fTyp = getSigT f typ
    return (I.Proj term f, addSubsts fTyp substs)
  else do
    (y,x) <- freshMetas g
    addConstr (PrjC g y x term typ f)
    return (y,x)

genExpC :: Gamma -> [Phi] -> ElabM (Term,Type)
genExpC g phis = do
  (y,x) <- freshMetas g
  addConstr (ExpC g y phis x)
  return (y,x)

genSubC :: Gamma -> [F] -> ElabM Term
genSubC g fs = do
  x <- freshMeta g I.Set
  addConstr (SubC g fs x)
  return x

-- Elaborate a list of constants to a new gamma with an associated meta store
elabSigma :: CSigma -> ElabM [(N,Term)]
elabSigma (CS cs) = go cs
  where go [] = return []
        go ((n,e): cs') = do -- let rems = go cs'; t = elaborate' consts e I.Set in (n,t) : rems
          t <- check (Gamma []) e I.Set 
          cs'' <- local (liftG ((n,t):)) (go cs')
          return $ (n,t) : cs''




-- TEMPORARY SHIT DOWN HERE, BEWARE ITS TEMPORARY NATURE AND LOATHE ITS LACK OF ELEGANCE

-- temporary sig test
sig :: Term -> Bool
sig (I.Sig _) = True
sig _       = False


getSubsts :: N -> Term -> Term -> [Substitution]
getSubsts f t (I.Sig bs) = map (\(I.Bind n _) -> Sub (I.Proj t n) n) (takeWhileInc (\(I.Bind n' _) -> n' /= f) bs)
getSubsts _ _ _          = error "You dare try to extract precious substs from anything but a sig? Fool!"


getSigT :: N -> Term -> Term
getSigT f _t@(I.Sig bs) = go bs
  where go [] = error $ "There is no field "++ f ++ " in :" ++ show _t
        go (I.Bind n t : bs') = if n == f then t else go bs'
getSigT _ _ = error "There are no fields in non-sigs Mr. Clever esq."

addSubsts :: Term -> [Substitution] -> Term
addSubsts t sbs = if t == I.Set then I.Set else foldr (\s -> flip I.Subst s) t sbs

takeWhileInc :: (a -> Bool) -> [a] -> [a]
takeWhileInc _ [] = []
takeWhileInc p (x:xs) = if p x then x : takeWhileInc p xs else [x]
