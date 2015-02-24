{-# LANGUAGE NoMonomorphismRestriction#-}
module Internal where

import Data.Maybe
import Data.List
import Util

type N = String
type F = String

data Substitution = Sub Term N
  deriving (Eq,Ord)

newtype Bind = Bind (N,Term)
  deriving (Eq,Ord)

type Type = Term


data Assign' = Ass N Term
  deriving (Eq,Ord)

data Assign = Pos Term | Named N Term 
  deriving (Eq,Ord)

data Phi = Phi Assign Type
  deriving (Eq,Ord)

instance Show Phi where
  show (Phi assn t) = show assn ++ " : " ++ show t


data Term = 
   Set
 | Cns N 
 | Var N
 | Fun (N,Term) Term
 | Lam (N,Term) Term
 | App Term Term
 | Sig [Bind]
 | Struct [Assign']
 | Proj Term N 
 | MetaTerm Meta
 | Subst Term Substitution
  deriving (Eq,Ord)

-- Metavariable with a name, type and static variable context
data Meta = Meta N Type Gamma
  deriving (Eq,Ord)

-- Variable context - doubles as Sigma
data Gamma = Gamma [(N,Term)]
  deriving (Eq,Ord)

instance Show Gamma where
  show (Gamma ls) = brack . intercalate ", " $ map go ls
    where go (n,t) = n ++ " : " ++ show t


-- I'm lazy
liftG :: ([(N,Term)] -> [(N,Term)]) -> Gamma -> Gamma
liftG f (Gamma ls) = Gamma (f ls)

--- Show instances

instance Show Term where
  show _t = case _t of
   Set -> "Set"
   Cns n -> "<"++n++">"
   Var n -> n
   Fun (n,t) t' -> par (n ++ " : " ++ show t) ++ " -> " ++ show t'
   Lam (n,t) t' -> "\\" ++ par (n ++ " : " ++ show t) ++ " -> " ++ show t'
   App t1 t2 -> show t1 ++ " " ++ show t2
   Sig bs -> "sig" ++ brace (intercalate "," (map show bs))
   Struct assn -> "struct" ++ brace (intercalate "," (map show assn))
   Proj t n -> show t ++ "." ++ n
   MetaTerm (Meta n _ _) -> n
   Subst t sub -> (show t) ++ brack (show sub)

instance Show Meta where
  show (Meta n t g) = par (n ++ ":" ++ show t) ++ brack (show g)

instance Show Bind where
  show (Bind (n,t)) = n ++ " : " ++ show t

instance Show Assign where
  show (Pos t) = show t
  show (Named n t) = n ++ " := " ++ show t

instance Show Assign' where
  show (Ass n t) = n ++ " := " ++ show t


instance Show Substitution where
  show (Sub t n) = show t ++ " / " ++ n

---

addBind :: (N,Term) -> Gamma -> Gamma
addBind a (Gamma bs) = Gamma (a:bs) 

data Xi = Xi {bindC :: Int, metaC :: Int, constraints :: [Constraint], metas :: [Meta]}

instance Show Xi where
  show (Xi _ _ constrs metas') = surround "[[\n" "\n]]" (go constrs ++ "\n\n--===--\n\n" ++ go metas')
    where go = unlines . map show

addConstraint :: Constraint -> Xi -> Xi
addConstraint c x = x{constraints=c : constraints x}

addMeta :: Meta -> Xi -> Xi
addMeta m xi = xi{metas=m:metas xi}

incMetaC :: Xi -> Xi
incMetaC x = x{metaC=metaC x + 1}

incBindC :: Xi -> Xi
incBindC x = x{bindC=bindC x + 1}


emptyXi :: Xi
emptyXi = Xi 0 0 [] []


data Constraint =
    ExpC Gamma Term [Phi] Type
  | SubC Gamma [F] Type
  | PrjC Gamma Term Type Term Type F
  | EquC Gamma Term Type Term Type
  deriving Ord

-- Looks like a DOS racing game ↓ 

instance Eq Constraint where
  ExpC _ _ _ _ == ExpC _ _ _ _ = True
  SubC _ _ _ == SubC _ _ _ = True
  PrjC _ _ _ _ _ _ == PrjC _ _ _ _ _ _ = True
  EquC _ _ _ _ _ == EquC _ _ _ _ _ = True
  _ == _ = False  

--

instance Show Constraint where
  show c = case c of
      ExpC g t phis tT -> par (show t ++ " <-- " ++ phis' ++ " |> " ++ show tT) ++ brack (show g)
        where phis' = brace (intercalate "," (map show phis))
      SubC g fs t -> par (show fs ++ " <_ " ++ show t) ++ brack (show g)
      PrjC g t _T t' _T' f -> par (show t ++ " : " ++ show _T ++ " <-- " ++ show t' ++ " : " ++ show _T' ++ "<" ++ f ++ ">") ++ brack (show g)
      EquC g _t _T _t' _T' -> par (show _t ++ " <-- " ++ show _t' ++ " : " ++ show _T ++ " = " ++ show _T') ++ brack (show g)
--

lookupG :: Gamma -> N -> Term
lookupG (Gamma ls) n = fromJust . lookup n $ ls
