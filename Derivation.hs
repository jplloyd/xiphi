{-# OPTIONS -Wall #-}
module Derivation where

import Types
import Util
import Internal

-- ##  Rule references ## ----------------------------------

-- Temporary structure - still working on this
data Rule = Indexed Rule' RuleIdx
          | Unindexed Rule'
          | Simple Rule'
          | InferRes Type Term RuleIdx
          | CheckRes Term RuleIdx

data RuleType = Infer | Check

-- Rules used in type checking - show instance will reference rules (eventually)
data Rule' =
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


-- Create a latex eqref for each rule
toEqRef :: Rule' -> String
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

