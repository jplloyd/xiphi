{-# LANGUAGE NoMonomorphismRestriction#-}
module Internal where

-- import Data.Maybe
import Data.List
import Util
import Types

-- Synonyms for environments

type Gamma = Env Ref
type Sigma = Env String

-- Substitution of a Term for a reference
data Substitution = Sub Term Ref
  deriving (Eq,Ord)

data IBind = IBind {ibF :: Field, ibTerm :: Term}
  deriving (Eq,Ord,Show)

-- Synonym used to mark when a term should be a type
type Type = Term

-- Named assignment 
data Assign' = Ass {assF :: Field, assTerm :: Term}
  deriving (Eq,Ord,Show)

-- Optionally named Assignment
data Assign = Pos Term | Named Field Term
  deriving (Eq,Ord)

-- Typed optionally named assignment
data Phi = Phi Assign Type
  deriving (Eq,Ord)

-- Term grammar
data Term = 
   ISet
 | ICns Name
 | IVar Ref
 | IFun (Ref,Type) Type
 | ILam (Ref,Type) Term
 | IApp Term Term
 | ISig [IBind]
 | IStruct [Assign']
 | IProj Term Field
 | IMeta Meta [Substitution]
  deriving (Eq,Ord,Show)

-- Metavariable with a name, type and static variable context
data Meta = Meta Int Type Gamma
  deriving (Eq,Ord)

-- NOTE: in order for the bind counter to be useful the value has to be initiated 
-- with at least one higher than the highest bind generated during scope checking.
data Xi = Xi {bindC :: Int, metaC :: Int, constraints :: [ContextConstraint], metas :: [Meta]}

-- Variable context
data Env a = Env [(a,Term)]
  deriving (Eq,Ord)

-- lift a context-modifying function
liftE :: ([(a,Term)] -> [(a,Term)]) -> Env a -> Env a
liftE f (Env ls) = Env (f ls)

--- Show instances
instance Show Phi where
  show (Phi assn t) = showAsgn assn ++ " : " ++ showTerm t

showTerm :: Term -> String
showTerm _t = case _t of
   ISet -> "Set"
   ICns n -> "<"++n++">"
   IVar n -> showRef n
   IFun (n,t) t' -> par (showRef n ++ " : " ++ showTerm t) ++ arrowRight ++ showTerm t'
   ILam (n,t) t' -> par $ "\\" ++ par (showRef n ++ " : " ++ showTerm t) ++ arrowRight ++ showTerm t'
   IApp t1 t2 -> par (showTerm t1) ++ " " ++ showTerm t2
   ISig bs -> "sig" ++ brace (intercalate "," (map showIB bs))
   IStruct assn -> "struct" ++ brace (intercalate "," (map showAsgn' assn))
   IProj t n -> showTerm t ++ "." ++ n
   IMeta (Meta n _ _) sb -> "_" ++ show n ++ if null sb then "" else " " ++ show sb

instance Show Meta where
  show (Meta n _ _) = "_" ++ show n

showMeta :: Meta -> String
showMeta (Meta n t g) = par ("_" ++ show n ++ " : " ++ showTerm t) -- ++ "\n\t\915 = " ++ showGamma g

showIB :: IBind -> String
showIB (IBind n t) = n ++ " : " ++ showTerm t

showAsgn :: Assign -> String
showAsgn (Pos t) = showTerm t
showAsgn (Named n t) = n ++ " := " ++ showTerm t


showAsgn' :: Assign' -> String
showAsgn' (Ass n t) = n ++ " := " ++ showTerm t


instance Show Substitution where
  show (Sub t n) = showTerm t ++ " / " ++ showRef n

-- Constraints and contexts

data ContextConstraint = CConstr Gamma Constraint

instance Show ContextConstraint where
  show (CConstr g c) =  show c -- ++ "\n\t\915 = " ++ showGamma g

-- The constraint shapes without their variable contexts
data Constraint =
    ExpC Type [Phi] Term           -- T<Phi> => Y
  | SubC Type [Field]              -- T<fv>
  | PrjC Type Term Field Term Type -- T<t.f> => Y : X
  | EquC Type Type Term Term       -- U = T ¦ X <- u
  deriving (Eq,Ord)

instance Show Constraint where
  show c = case c of
    ExpC _T phis _Y -> "XP " ++ showTerm _T ++ angBr (show phis) ++ rightDblArr ++ showTerm _Y
    SubC _T fs     -> "SB " ++ showTerm _T ++ angBr (show fs)
    PrjC _T t f _Y _X -> "PR " ++ showTerm _T ++ angBr (showTerm t ++ "." ++ f)
                         ++ rightDblArr ++ " " ++ showTerm _Y ++ " : " ++ showTerm _X
    EquC _U _T _X u -> "EQ " ++ par (showTerm _U ++ " = " ++ showTerm _T)
                       ++ "\8224" ++  -- dagger
                       par (showTerm _X ++ arrowLeft ++ showTerm u)

showGamma (Env ls) = brack . intercalate ", " . reverse $ map go ls
    where go (n,t) = showRef n ++ " : " ++ showTerm t


instance Show a => Show (Env a) where
  show (Env ls) = brack . intercalate ", " . reverse $ map go ls
    where go (n,t) = show n ++ " : " ++ showTerm t

instance Show Xi where
  show (Xi _ _ constrs metas') = surround "[[\n" "\n]]\n" ("\n== Constraints == \n\n" ++ go constrs ++ "\n== Metavariables ==\n\n" ++ go1 metas') ++ summary
    where go = unlines . map show . reverse
          go1 = unlines . map showMeta . reverse
          summary = "Number of metas: " ++ show (length metas') ++ "\nNumber of constraints: " ++ show (length constrs)

-- Check if a term is final (no metavariables), as should be the case post-unification
isFinal :: Term -> Bool
isFinal _t = case _t of
   ISet -> True
   ICns _ -> True
   IVar _ -> True
   IFun (_,t) t' -> isFinal t && isFinal t'
   ILam (_,t) t' -> isFinal t && isFinal t'
   IApp t1 t2 -> isFinal t1 && isFinal t2
   ISig bs -> all isFinal (map ibTerm bs)
   IStruct assn -> all isFinal (map assTerm assn)
   IProj t _ -> isFinal t
   IMeta _ _ -> False

-- Add a bind to an environment
addBind :: (Ref,Term) -> Gamma -> Gamma
addBind a (Env bs) = Env (a:bs)

-- Add multiple binds to an environment
addBinds :: [(Ref,Term)] -> Gamma -> Gamma
addBinds as (Env bs) = Env (as ++ bs)

addConstraint :: ContextConstraint -> Xi -> Xi
addConstraint c x = x{constraints=c : constraints x}

addMeta :: Meta -> Xi -> Xi
addMeta m xi = xi{metas=m:metas xi}

incMetaC :: Xi -> Xi
incMetaC x = x{metaC=metaC x + 1}

incBindC :: Xi -> Xi
incBindC x = x{bindC=bindC x + 1}

emptyXi :: Xi
emptyXi = Xi 0 0 [] []

-- Look something up in an environment
lookupE :: (Ord a) => a -> Env a -> Maybe Term
lookupE n (Env ls) = lookup n ls
