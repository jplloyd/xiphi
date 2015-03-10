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
  deriving (Eq,Ord)

-- Synonym used to mark when a term should be a type
type Type = Term

-- Named assignment 
data Assign' = Ass {assF :: Field, assTerm :: Term}
  deriving (Eq,Ord)

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
 | ILam (Ref,Term) Term
 | IApp Term Term
 | ISig [IBind]
 | IStruct [Assign']
 | IProj Term Field
 | IMeta Meta [Substitution]
  deriving (Eq,Ord)

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
  show (Phi assn t) = show assn ++ " : " ++ show t

instance Show Term where
  show _t = case _t of
   ISet -> "Set"
   ICns n -> "<"++n++">"
   IVar n -> show n
   IFun (n,t) t' -> par (show n ++ " : " ++ show t) ++ " -> " ++ show t'
   ILam (n,t) t' -> "\\" ++ par (show n ++ " : " ++ show t) ++ " -> " ++ show t'
   IApp t1 t2 -> show t1 ++ " " ++ show t2
   ISig bs -> "sig" ++ brace (intercalate "," (map show bs))
   IStruct assn -> "struct" ++ brace (intercalate "," (map show assn))
   IProj t n -> show t ++ "." ++ n
   IMeta (Meta n _ _) sb -> "_" ++ show n -- PRINT OUT SUBSTITUTIONS IN SOME NICE WAY

instance Show Meta where
  show (Meta n t g) = par ("_" ++ show n ++ " : " ++ show t) ++ "\n\t\915 = " ++ show g

instance Show IBind where
  show (IBind n t) = n ++ " : " ++ show t

instance Show Assign where
  show (Pos t) = show t
  show (Named n t) = n ++ " := " ++ show t

instance Show Assign' where
  show (Ass n t) = n ++ " := " ++ show t

instance Show Substitution where
  show (Sub t n) = show t ++ " / " ++ show n

-- Constraints and contexts

data ContextConstraint = CConstr Gamma Constraint

instance Show ContextConstraint where
  show (CConstr g c) =  show c ++ "\n\t\915 = " ++ show g

-- The constraint shapes without their variable contexts
data Constraint =
    ExpC Type [Phi] Term           -- T<Phi> => Y
  | SubC Type [Field]              -- T<fv>
  | PrjC Type Term Field Term Type -- T<t.f> => Y : X
  | EquC Type Type Term Term       -- U = T ¦ X <- u
  deriving (Eq,Ord)

instance Show Constraint where
  show c = case c of
    ExpC _T phis _Y -> show _T ++ angBr (show phis) ++ rightDblArr ++ show _Y
    SubC _T fs     -> show _T ++ angBr (show fs)
    PrjC _T t f _Y _X -> show _T ++ angBr (show t ++ "." ++ f)
                         ++ rightDblArr ++ " " ++ show _Y ++ " : " ++ show _X
    EquC _U _T _X u -> par (show _U ++ " = " ++ show _T)
                       ++ "\8224" ++  -- dagger
                       par (show _X ++ "\8592" ++ show u)

instance Show a => Show (Env a) where
  show (Env ls) = brack . intercalate ", " . reverse $ map go ls
    where go (n,t) = show n ++ " : " ++ show t

instance Show Xi where
  show (Xi _ _ constrs metas') = surround "[[\n" "\n]]" (go constrs ++ "\n--===--\n\n" ++ go metas')
    where go = unlines . map show . reverse

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
