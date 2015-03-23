module Derivation where

import Types
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
   CheckGen -- eq:checkrule
 | EqRedRefl -- eq:algeqrefl
 | EqRedGenC -- eq:addceq
-- ============================
 | InferSet -- eq:infset
 | InferCns -- eq:infc
 | InferVar -- eq:infv
 | InferWld -- eq:infunderscore
 | InferFun -- eq:inffuntyp
 | InferRecB -- eq:infrectypbas
 | InferRecC -- eq:infrectyprec
-- ====================
 | InferApp -- eq:infapp
 | AppKnown -- eq:appknown
 | AppUnknown -- eq:appunknown
-- ==========================
 | InferLam -- eq:infexplambda
 | SubSeqGenC -- eq:xiopssubs
-- ==========================
 | InferEStr -- eq:infexprec
 | InferPhiS -- eq:infphi
 | ExpGenC -- eq:xiopsstexp
-- ==========================
 | InferProj -- eq:infproj
 | ProjRed -- eq:unifprojconstraint
 | ProjGenC -- eq:xiopsproj
-- ==========================
 | FreshMeta -- Xi Operations <
 | FreshMetas --              <
 | AddConstraint --           <
-- ============================
  deriving Show

toEqRef :: Rule' -> String
toEqRef r = case r of
  CheckGen -- eq:checkrule
  EqRedRefl -- eq:algeqrefl
  EqRedGenC -- eq:addceq

  InferSet -- eq:infset
  InferCns -- eq:infc
  InferVar -- eq:infv
  InferWld -- eq:infunderscore
  InferFun -- eq:inffuntyp
  InferRecB -- eq:infrectypbas
  InferRecC -- eq:infrectyprec

  InferApp -- eq:infapp
  AppKnown -- eq:appknown
  AppUnknown -- eq:appunknown

  InferLam -- eq:infexplambda
  SubSeqGenC -- eq:xiopssubs

  InferEStr -- eq:infexprec
  InferPhiS -- eq:infphi
  ExpGenC -- eq:xiopsstexp

  InferProj -- eq:infproj
  ProjRed -- eq:unifprojconstraint
  ProjGenC -- eq:xiopsproj

  FreshMeta -- Xi Operations <
  FreshMetas --              <
  AddConstraint --           <

