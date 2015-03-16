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
fails = chkTy $ lamgappf vg
hacks = chkTy $ lamgappf (SLam [_b] _t $ SApp vg [SPos vb] vt)
-- where
chkTy e = ChkProb postulate e eTy
lamgappf = elam1 _g . eapp1 cf


-- TCProb with optional solutions

-- Identifiers
_T = "T"
_b = "b"
_f = "f"
_g = "g"
_t = "t"
_z = "z"

-- Constants
cf = SCns _f

-- Variables
vT = SVar _T
vb = SVar _b
vg = SVar _g
vt = SVar _t
vz = SVar _z

-- Bindings
bTSetSet = SBind _T (fun dSet SSet)
bbSet = SBind _b SSet

-- Dummy bindings
dSet = dummy SSet

-- Function abstractions
-- eid = elam1 _z vz

-- Applications
appT = eapp1 vT

-- Convenience functions
eapp1 fe ae1 = SApp fe [] ae1

elam1 n1 e = SLam [] n1 e

dummy = SBind "£"

fun = SFun []
