module HTy where

import Surface
import CheckHub


-- Named expressions
eTy = SFun impl expl cod
  where impl = [bTSetSet]
        expl = dummy $ SFun [bASet] (dummy $ appT vA) SSet
        cod  = SSet

-- Postulates
postulate =
  [(_f, eTy)]

-- Type checking problems
simple = ChkProb postulate SSet SSet

works = chkTy cf
solva = chkTy $ lamg []   []        vg
unsol = chkTy $ lamg []   []        (lamta [] [])
giveT = chkTy $ lamg [_T] [SPos vT] (lamta [] [])
giveA = chkTy $ lamg []   []        (lamta [_A] [SPos vA])

solva_ = chkTy $ lamgT [SPos SWld] vg
unsol_ = chkTy $ lamgT [SPos SWld] (lamtaA [SPos SWld])
giveT_ = chkTy $ lamgT [SPos vT]   (lamtaA [SPos SWld])
giveA_ = chkTy $ lamgT [SPos SWld] (lamtaA [SPos vA])

-- where
chkTy e = ChkProb postulate e eTy
lamgT  = lamg  [_T]
lamtaA = lamta [_A]
lamg = lam _g cf
lamta impls args = lam _ta vg impls args vta
lam bind fun impls args = SLam impls bind . SApp fun args


-- Identifiers
_T  = "T"
_A  = "A"
_f  = "f"
_g  = "g"
_ta = "ta"

-- Constants
cf = SCns _f

-- Variables
vT  = SVar _T
vA  = SVar _A
vg  = SVar _g
vta = SVar _ta

-- Bindings
bTSetSet = SBind _T (fun dSet SSet)
bASet = SBind _A SSet

-- Dummy bindings
dSet = dummy SSet

-- Applications
appT = eapp1 vT

-- Convenience functions
eapp1 fe ae1 = SApp fe [] ae1

elam1 n1 e = SLam [] n1 e

dummy = SBind "\\_"

fun = SFun []

