module Ty where

import Surface
import CheckHub


-- Named expressions
eTy = SFun impl expl cod
  where impl = [bTSetSet]
        expl = dummy $ SFun [bbSet] (dummy $ appT vb) (appT SSet)
        cod  = SSet

-- Postulates
postulate =
  [(_f, eTy)]

-- Type checking problems
simple = ChkProb postulate SSet SSet
works = chkTy cf
fails = chkTy $ lamg []   []          vg
failz = chkTy $ lamg [_T] []          (lambt [])
failc = chkTy $ lamg [_T] [SPos SWld] (lambt [SPos SWld])
hacks = chkTy $ lamg []   []          (lambt [SPos vb])
hackz = chkTy $ lamg [_T] [SPos vT]   vg
-- where
chkTy e = ChkProb postulate e eTy
lamg = lam _g cf
lambt args = lam _t vg [_b] args vt
lam bind fun implbinds implargs = SLam implbinds bind . SApp fun implargs


-- Identifiers
_T = "T"
_b = "b"
_f = "f"
_g = "g"
_t = "t"

-- Constants
cf = SCns _f

-- Variables
vT = SVar _T
vb = SVar _b
vg = SVar _g
vt = SVar _t

-- Bindings
bTSetSet = SBind _T (fun dSet SSet)
bbSet = SBind _b SSet

-- Dummy bindings
dSet = dummy SSet

-- Applications
appT = eapp1 vT

-- Convenience functions
eapp1 fe ae1 = SApp fe [] ae1

elam1 n1 e = SLam [] n1 e

dummy = SBind "£"

fun = SFun []

