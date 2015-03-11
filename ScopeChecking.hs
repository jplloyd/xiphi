module ScopeChecking where

import DList
import Surface as S
import Core as C
import Types

import Data.Functor
import Data.Tuple

import Control.Monad.Trans.Writer
import Control.Monad.State
import Control.Monad.Reader
import Control.Monad.Except

-- Context and operations

data Context = Context {vCounter :: Int, rCounter::Int}

emptyC :: Context 
emptyC = Context 0 0

incF :: Context -> Context
incF c = c{rCounter=rCounter c + 1}

incV :: Context -> Context
incV c = c{vCounter = vCounter c + 1}

freshVarBind :: SCM Ref
freshVarBind = do
  vc <- vCounter <$> get
  modify incV
  return $ var vc

freshRecBind :: SCM Ref
freshRecBind = do
  vc <- rCounter <$> get
  say $ "Creating a fresh record bind:" ++ show vc
  modify incF
  return $ rec vc

-- Substitutions (CExpr for variables) and related operations

type Substitution = (N,CExpr)

type Theta = [Substitution]

addBind :: Substitution -> SCM a -> SCM a
addBind s = local (s:)

addBinds  :: Theta -> SCM a -> SCM a
addBinds ss = local (ss ++)

getSubstitute :: N -> SCM CExpr
getSubstitute n = do
  say $ "Looking up the replacement for " ++ n
  subs <- ask
  let cexpr = lookup n subs
  let go (Just n') = say ("Found the replacement: " ++ show n') >> return n'
      go Nothing  = throwError $ "Referenced variable out of scope: " ++ n
  go cexpr

-- Substitution context
type SubT = ReaderT Theta

-- Global counters
type Cntx = State Context

-- Scope checking monad
type SCM = ErrT (LogT (SubT Cntx))

-- Add message in the writer, separated by newline
say :: String -> SCM ()
say s = lift $ tell (toDList (s++"\n"))

-- Initate scope checking
-- This can easily be written on one line, and anyone doing so will quickly regret it
scopecheck :: SExpr -> (Log,Either Error CExpr)
scopecheck e = swap res4
  where res1 = runExceptT . scopecheck' $ e
        res2 = runWriterT res1
        res3 = runReaderT res2 []
        res4 = evalState res3 emptyC

-- Scope checking within the SCM monad
scopecheck' :: SExpr -> SCM CExpr
scopecheck' _e = case _e of
  SSet -> say "Transforming Set" >> return CSet
  SCns n -> say ("Transforming the constant: " ++ n) >> return (CCns n)
  SVar n -> say ("Attempting to transform variable: " ++ n) >> getSubstitute n
  SFun impl (SBind n e) cod -> do
    say ("Transforming the function type: " ++ show _e)
    sig@(CSig bs) <- makeSig impl
    r <- freshRecBind
    let recSubsts = map (\(FBind n' _) -> (n', CProj (CVar r) n')) bs
    say "Adding substitutions for references to the implicits, then checking the explicit argument."
    v <- freshVarBind
    e' <- addBinds recSubsts $ scopecheck' e
    say "Adding the substitution for the explicit binding and checking the codomain."
    cod' <- addBinds ((n, CVar v):recSubsts) $ scopecheck' cod
    return $ CFun (CBind r sig) (CFun (CBind v e') cod')
  SApp e impl e' -> do
    say $ "Transforming application: " ++ show _e
    e1 <- scopecheck' e
    estr <- makeEstruct impl
    e2 <- scopecheck' e'
    return $ CApp (CApp e1 estr) e2
  SLam impls expl e -> do
    say $ "Transforming lambda abstraction: " ++ show _e
    unique impls
    r <- freshRecBind
    v <- freshVarBind
    let recsubsts = (expl, CVar v) : map (\f -> (f, CProj (CVar r) f)) impls
    e' <- addBinds recsubsts (scopecheck' e)
    return $ CLam r (FL impls) v e'
  SWld -> say "Transforming wildcard..." >> return CWld

    
-- Auxiliary function to create record types
makeSig :: [SBind] -> SCM CExpr
makeSig bs = do
  say "Converting implicit binds to a record type"
  say "Checking that binds are locally unique"
  unique $ bindsOf bs
  CSig <$> go bs
    where go :: [SBind] -> SCM [FBind]
          go [] = return []
          go (SBind n e: bs') = do
            ce <- scopecheck' e
            rm <- addBind (n, CVar . field $ n) $ go bs'
            return $ FBind n ce : rm

-- Helper extracting names from lists of bindings
bindsOf :: [SBind] -> [N] 
bindsOf = map (\(SBind n _) -> n)

-- Auxiliary function to create expandable records
makeEstruct :: [SAssign] -> SCM CExpr
makeEstruct sa = CEStr <$> go [] sa
  where go :: [Field] -> [SAssign] -> SCM [CAssign]
        go taken as = case as of
          [] -> return []
          SNamed n e : as' ->
            if elem n taken
            then throwError ("Duplicate field in assignment: " ++ n)
            else do
              e' <- scopecheck' e
              rs <- go (n:taken) as'
              return (CNamed n e' : rs)
          SPos e : as' -> do
            e' <- scopecheck' e
            rs <- go taken as'
            return (CPos e' : rs)

-- Uniqueness test for elements of a list - failing on first repetition
unique :: (Eq a,Show a) => [a] -> SCM ()
unique ls = say ("Checking uniqueness for the elements: " ++ show ls) >> go [] ls
  where go _ [] = void (say "All elements were unique")
        go ex (x:xs) = if x `elem` ex
                       then throwError $ "Duplicate element: " ++ show x ++ "!"
                       else go (x:ex) xs
