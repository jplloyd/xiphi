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
   IFun (n,t) t' -> par $ par (showRef n ++ " : " ++ showTerm t) ++ arrowRight ++ showTerm t'
   ILam (n,t) t' -> par $ "\\" ++ par (showRef n ++ " : " ++ showTerm t) ++ arrowRight ++ showTerm t'
   IApp t1 t2 -> par (showTerm t1) ++ " " ++ showTerm t2
   ISig bs -> "sig" ++ brace (intercalate "," (map showIB bs))
   IStruct assn -> "struct" ++ brace (intercalate "," (map showAsgn' assn))
   IProj t n -> showTerm t ++ "." ++ n
   IMeta (Meta n _ _) sb -> "_" ++ show n ++ if null sb then "" else " " ++ show sb


-- Latex printing

-- Place as underset to a variable
underset :: String -> String -> String
underset v uset = v ++ "_{" ++ uset ++"}"


mathit :: String -> String
mathit s = "\\mathit{" ++ s ++ "}"


-- These things have to be in math context in order to compile
latexTerm :: Term -> String
latexTerm _t = case _t of
   ISet -> mathit "Set"
   ICns n -> mathit n
   IVar n -> latexRef n
   IFun (n,t) t' -> (par $ (latexRef n) ++ ":" ++ latexTerm t) ++ " -> " ++ latexTerm t'
   ILam (n,t) t' -> "\\lambda " ++ par (latexRef n ++ ":" ++ latexTerm t) ++ " -> " ++ par (latexTerm t')
   IApp t1 t2 -> (latexTerm t1) ++ "\\fsp" ++ par (latexTerm t2) -- this only needs to be parenthesized if it is an app I think
   ISig bs -> "\\sig{" ++ intercalate "," (map latexBs bs) ++ "}"
   IStruct assn -> "\\struct{" ++ intercalate "," (map latexAssn' assn) ++ "}"
   IProj t n -> latexTerm t ++ "." ++ mathit n
   IMeta (Meta n _ _) sb -> underset "X" (show n) -- possibly include substitutions

latexBs :: IBind -> String
latexBs (IBind n t) = mathit n ++ ":" ++ latexTerm t

latexAssn' :: Assign' -> String
latexAssn' (Ass f t) = mathit f ++ " := " ++ latexTerm t

latexAssn :: Assign -> String
latexAssn a = case a of
  Pos t -> latexTerm  t
  Named f t -> mathit f ++ "=" ++ latexTerm t

latexConstraint :: Constraint -> String
latexConstraint c = case c of 
    ExpC _T phis _Y -> latexTerm _T ++ "< " ++ latexPhis phis ++ " > " ++ " \red " ++ latexTerm _Y
    SubC _T fs     -> latexTerm _T ++ " < " ++ latexFields fs ++ " > "
    PrjC _T t f _Y _X -> latexTerm _T ++ " < " ++ (latexTerm t ++ "." ++ mathit f) ++ " > "
                         ++ " \red " ++ latexTerm _Y ++ " : " ++ latexTerm _X
    EquC _U _T _X u -> par (latexTerm _U ++ " \\eq " ++ latexTerm _T)
                       ++ " \\locks " ++  -- dagger
                       par (latexTerm _X ++ " <- " ++ latexTerm u)

latexPhis :: [Phi] -> String
latexPhis phis = intercalate "," $ map latexPhi phis
  where latexPhi (Phi asgn _T) = latexAssn asgn ++ ":" ++ latexTerm _T

latexFields :: [String] -> String
latexFields fields = intercalate "," fields

latexRef :: Ref -> String
latexRef (V g idx) = flip underset (show idx) $ case g of
  VarBind -> "x"
  RecBind -> "r"
  Unknown -> "u" -- should not be part of output post-resolution

-- end of latex printing


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

data ContextConstraint = CConstr {context :: Gamma, constraint ::  Constraint}

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
