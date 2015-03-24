{-# LANGUAGE TypeSynonymInstances#-}
{-# OPTIONS -Wall #-}
module Derivation where

import Types
import Util
import Internal
import Core
import LatexPrint

-- ##  Rule references ## ----------------------------------

-- Special symbols for derivation notation

-- semi-circle facing left (checking)
chkStart :: RuleIdx -> Latex
chkStart idx = preScriptT (lP idx) $ ltx "\\lceil"

-- semi-circle facing right (inference)
infStart :: RuleIdx -> Latex
infStart idx = preScriptT (lP idx) $ ltx "\\llceil"

-- Checking double arrows
lChk :: Latex
lChk = ltx "\\leftleftarrows"

-- Inference double arrows
lInf :: Latex
lInf = ltx "\\rightrightarrows"

-- leads to macro
leadsTo :: Latex
leadsTo = ltx "~>" -- ltx "\\leadsto"

-- beginning of a multiline derivation
startI :: Latex
startI = ltx "\\rrceil"

startC :: Latex
startC = ltx "\\rceil"


-- result (output) of a multiline derivation
endI :: Latex
endI = ltx "\\llfloor"

endC :: Latex
endC = ltx "\\lfloor"


-- double bracket right (single line derivation)
comp :: Latex
comp = ltx "\\rrbracket"


-- post only
-- place first argument as superscript of second argument
superScript :: Latex -> Latex -> Latex
superScript s inp = inp <++> lLift (surround "^{" "}") s

-- subscript only
preScriptS :: Latex -> Latex -> Latex
preScriptS p inp = lLift (surround "\\prescript{}{" "}") p <++> (lLift brace) inp

preScriptT :: Latex -> Latex -> Latex
preScriptT p inp = lLift (surround "\\prescript{" "}{}") p <++> (lLift brace) inp

startMulti :: Latex -> RuleIdx -> Latex
startMulti start idx = superScript (lP idx) start

endMulti :: Latex -> RuleIdx -> Latex
endMulti end idx = preScriptS (lP idx) end


-- constructor synonyms

infInd :: CExpr -> RuleName -> RuleIdx -> Rule
infInd e = Indexed e InfInd

chkInd :: CExpr -> Type -> RuleName -> RuleIdx -> Rule
chkInd e _T = Indexed e (ChkInd _T)

infCmp :: CExpr -> RuleName -> [RuleName] -> Type -> Term -> Rule
infCmp e rn rs _T t = Compact e (InfCmp _T t) rn rs 

chkCmp :: CExpr -> Type -> RuleName -> [RuleName] -> Term -> Rule
chkCmp e _T rn rs t = Compact e (ChkCmp _T t) rn rs

infRes :: Type -> Term -> RuleIdx -> Rule
infRes _T t = Result (InfRes _T t)

chkRes :: Term -> RuleIdx -> Rule
chkRes = Result . ChkRes

-- Different types of rules for printing (rules may be compacted where appropriate)
data Rule = Indexed CExpr IndT RuleName RuleIdx -- Beginning of an inference with relevant rule
          | Compact CExpr CmpT RuleName [RuleName] -- Single line rules
          | Simple RuleName -- Just an eqref to the rule (input/output redundant)
          | Result ResT RuleIdx -- Result (multiline)
          | Delimiter
  deriving Show
           
isSimple :: Rule -> Bool
isSimple r = case r of
  (Simple _) -> True
  _          -> False

ruleName :: Rule -> RuleName
ruleName r = case r of
  Indexed _ _ rn _ -> rn
  Compact _ _ rn _ -> rn
  Simple rn -> rn
  _ -> error $ show r ++ " does not have a stored rule name (getRuleName)"

-------------------

data ResT = ChkRes Term | InfRes Type Term
  deriving Show

data IndT = ChkInd Type | InfInd
  deriving Show

data CmpT = ChkCmp Type Term | InfCmp Type Term
  deriving Show

-------------------

compactT :: IndT -> ResT -> CmpT
compactT (ChkInd _T) (ChkRes t) = ChkCmp _T t
compactT InfInd (InfRes _T t) = InfCmp _T t
compactT _ _ = error "Illegal compaction pair"

-- naive compaction algorithm

compact :: [Rule] -> [Rule]
compact [] = []
compact (r:rs) = case r of
  (Indexed e typ rn idx) -> if all isSimple steps
                            then simplified
                            else r : compact rs
    where (steps,rT,rs') = getSteps idx rs
          simplified = Compact e (compactT typ rT) rn
                       (map ruleName steps) : compact rs'
  _ -> r : compact rs

getSteps :: RuleIdx -> [Rule] -> ([Rule],ResT,[Rule])
getSteps idx = go []
  where go _ [] = error $ "There was no matching result for multiline rule: " ++ show idx
        go acc (Result rT idx':rs') | idx == idx' = (reverse acc, rT, rs')
        go acc (rl:rs') = go (rl:acc) rs'

------------------
        
instance LatexPrintable Rule where
  latexPrint Delimiter = ltx "\\pagebreak"
  latexPrint r = lLift (surround "$" "$") $ case r of
    Indexed e InfInd        rn idx -> infStart idx <©> lP e <©> startMulti startI idx <©> lP rn
    Indexed e (ChkInd _T) rn idx -> chkStart idx <©> lP e <©> lChk <©> lP _T <©> startMulti startC idx <©> lP rn
    Compact e (InfCmp _T t) rn rs -> ltx "\\llbracket" <©> lP e <©> comp <©> lP rn <©> lConc (map lP rs)
                               <©> lInf <©> lP _T <©> leadsTo <©> lP t
    Compact e (ChkCmp _T t) rn rs-> ltx "[" <©> lP e <©> lChk <©> lP _T <©> ltx "]" <©> lP rn 
                               <©> lConc (map lP rs) <©> leadsTo <©> lP t
    Simple rn -> lP rn
    Result (InfRes _T t) idx -> endMulti endI idx <©> lInf <©> lP _T <©> leadsTo <©> lP t
    Result (ChkRes t) idx -> endMulti endC idx <©> leadsTo <©> lP t

-- somewhat redundant (and orphan instance)
instance LatexPrintable RuleIdx where
  latexPrint  = ltx . show

  -- Rules used in type checking - show instance will reference rules (eventually)
data RuleName =
   CheckGen -- general checking
 | CheckLam -- special rule for lambdas
 | CheckExpB -- special rule for records (base)
 | CheckExpC -- special rule for records (cons)
 | ExpMatch -- matching a field in record expansion
 | ExpNoMatch -- not matching a field in record expansion
 | CheckWld -- special rule for wildcards
 | EqRedRefl -- equality reduction by reflexivity
 | EqRedGenC -- equality handling by constraint generation
-- ===========
 | InferSet -- infer Set
 | InferCns -- infer a constant
 | InferVar -- infer a variable
 | InferWld -- infer an underscore
 | InferFun -- infer a function type
 | InferSigB -- infer a record type (I guess)
 | InferSigC
-- ===========
 | InferApp -- infer a function application
 | AppKnown -- Type of head is known (in application)
 | AppUnknown -- Type of head is not known
-- ===========
 | InferLam -- infer a lambda (unused)
 | InferESig -- infer an expandable signature
 | UnifSolveSub -- verify subsequence relation
 | SubSeqGenC -- generate a subsequence constraint
-- ===========
 | InferEStr -- infer an expandable struct (unused?)
 | InferPhiS -- infer a vector of phi
 | ExpGenC -- create an expansion constraints (unused)
-- ===========
 | InferProj -- infer a projection
 | ProjRed -- immediate projection reduction
 | ProjGenC -- projection constraint (unused?)
-- ===========
 | FreshMeta -- create a fresh metavariable with a known type
 | FreshMetas -- create a fresh metavariable with an unknown type
 | AddConstraint -- add a constraint to the store
-- ===========
 | GenSubst
  deriving Show

instance LatexPrintable RuleName where
  latexPrint = ltx . toEqRef

-- Create a latex eqref for each rule
toEqRef :: RuleName -> String
toEqRef r = surround "\\eqref{" "}" $ case r of
  CheckLam -> "eq:chklam"
  CheckExpB -> "eq:chkrecbase"
  CheckExpC -> "eq:chkreccons"
  CheckWld -> "eq:chkunderscore"
  CheckGen -> "eq:chkgenexp"

  ExpMatch -> "eq:chkmatch"
  ExpNoMatch -> "eq:chknomatch" 

  EqRedRefl -> "eq:algeqrefl"
  EqRedGenC -> "eq:addceq"

  InferSet -> "eq:infset"
  InferCns -> "eq:infc"
  InferVar -> "eq:infv"
  InferWld -> "eq:infunderscore"
  InferFun -> "eq:inffuntyp"
  InferSigB -> "eq:infrectypbas"
  InferSigC -> "eq:infrectyprec"

  InferApp -> "eq:infapp"
  AppKnown -> "eq:appknown"
  AppUnknown -> "eq:appunknown"

  InferLam -> "eq:infexplambda"
  InferESig -> "eq:infesig"
  UnifSolveSub -> "eq:unifsolvesubs"
  SubSeqGenC -> "eq:xiopssubs"

  InferEStr -> "eq:infexprec"
  InferPhiS -> "eq:infphi"
  ExpGenC -> "eq:xiopsstexp"

  InferProj -> "eq:infproj"
  ProjRed -> "eq:unifprojconstraint"
  ProjGenC -> "eq:xiopsproj"

  FreshMeta -> "eq:xiopsintro1"
  FreshMetas -> "eq:xiopsintro2"
  AddConstraint -> "eq:xiaddc"

  GenSubst -> "eq:111"
