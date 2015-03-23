{-# LANGUAGE TypeSynonymInstances#-}
module Derivation where

import Types
import Util
import Internal
import Core
import LatexPrint

-- ##  Rule references ## ----------------------------------

-- Special symbols for derivation notation

-- semi-circle facing left (checking)
chkStart :: Latex
chkStart = ltx "\\llparenthesis"

-- semi-circle facing right (inference)
infStart :: Latex
infStart = ltx "\\rrparenthesis"

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
start :: Latex
start = ltx "\\rrceil"

-- result (output) of a multiline derivation
end :: Latex
end = ltx "\\llfloor"

-- double bracket right (single line derivation)
comp :: Latex
comp = ltx "\\rrbracket"


-- post only
-- place first argument as superscript of second argument
superScript :: Latex -> Latex -> Latex
superScript s inp = inp <++> lLift (surround "^{" "}") s

-- subscript only
preScript :: Latex -> Latex -> Latex
preScript p inp = lLift (surround "\\prescript{}{" "}") p <++> lxBrace inp

startMulti :: RuleIdx -> Latex
startMulti idx = superScript (lP idx) start

endMulti :: RuleIdx -> Latex
endMulti idx = preScript (lP idx) end

-- Different types of rules for printing (rules may be compacted where appropriate)
data Rule = InfIndexed CExpr RuleName RuleIdx -- Beginning of an inference with relevant rule
          | ChkIndexed CExpr Type RuleName RuleIdx -- Beginning of a checking with relevant rule
          | InfCompact CExpr RuleName [RuleName] Type Term -- One-line inference
          | ChkCompact CExpr Type RuleName [RuleName] Term -- One-line checking
          | Simple RuleName -- Just an eqref to the rule
          | InferRes Type Term RuleIdx -- Result of inference
          | CheckRes Term RuleIdx -- Result of checking

-- consider surrounding everything in math context
instance LatexPrintable Rule where
  latexPrint r = case r of -- maybe factor our the first four
    InfIndexed e rn idx -> infStart <©> lP e <©> startMulti idx <©> lP rn
    ChkIndexed e _T rn idx -> chkStart <©> lP e <©> lChk <©> lP _T <©> startMulti idx <©> lP rn
    -- could boldface the main rule to differentiate (but will always be first)
    InfCompact e rn rs _T t -> infStart <©> lP e <©> comp <©> lP rn <©> lConc (map lP rs)
                               <©> lInf <©> lP _T <©> leadsTo <©> lP t
    ChkCompact e _T rn rs t -> chkStart <©> lP e <©> lChk <©> lP _T <©> comp <©> lP rn <©>
                               lConc (map lP rs) <©> leadsTo <©> lP t
    Simple rn -> lP rn
    InferRes _T t idx -> endMulti idx <©> lInf <©> lP _T <©> leadsTo <©> lP t
    CheckRes t idx -> endMulti idx <©> leadsTo <©> lP t

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
 | InferRecB -- infer a record 
 | InferRecC
-- ===========
 | InferApp -- infer a function application
 | AppKnown -- Type of head is known (in application)
 | AppUnknown -- Type of head is not known
-- ===========
 | InferLam -- infer a lambda (unused)
 | SubSeqGenC -- generate a subsequence constraint (unused)
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
  CheckGen -> "eq:checkrule"

  ExpMatch -> "eq:chkmatch"
  ExpNoMatch -> "eq:chknomatch" 

  EqRedRefl -> "eq:algeqrefl"
  EqRedGenC -> "eq:addceq"

  InferSet -> "eq:infset"
  InferCns -> "eq:infc"
  InferVar -> "eq:infv"
  InferWld -> "eq:infunderscore"
  InferFun -> "eq:inffuntyp"
  InferRecB -> "eq:infrectypbas"
  InferRecC -> "eq:infrectyprec"

  InferApp -> "eq:infapp"
  AppKnown -> "eq:appknown"
  AppUnknown -> "eq:appunknown"

  InferLam -> "eq:infexplambda"
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

