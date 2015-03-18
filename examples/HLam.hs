module HLam where

import Surface
import CheckHub

-- Postulates
postulates =
  [(_Eq, fun dSet SSet)
  ,(_eq, fun bTSet (appEq vT))
  
  ,(_w, funTSet dEq_T (fun dT    SSet))
  ,(_f, funTSet dT    (fun dEq_T SSet))
  ]

-- Polymorphic id type
eId = funASet dA vA
-- Monomorphic id which is to be turned polymorphic
eid = elam1 _x vx

-- Type checking problems
simple n = ChkProb (take n postulates) SSet SSet

linear = chkSet (eapp2 cw eq_Id eid  )
nonlin = chkSet (eapp2 cf eid   eq_Id)
-- where
chkSet e = ChkProb postulates e SSet

-- Identifiers
_Eq = "Eq"
_eq = "eq"
_T = "T"
_A = "A"
_a = "a"
_w = "w"
_f = "f"
_x = "x"

-- Constants
cEq = SCns _Eq
ceq = SCns _eq
cw = SCns _w
cf = SCns _f

-- Variables
vT = SVar _T
vA = SVar _A
va = SVar _a
vx = SVar _x

-- Bindings
bTSet = SBind _T SSet
bASet = SBind _A SSet
baA = SBind _a vA

-- Dummy bindings
dSet = dummy SSet
dT = dummy vT
dA = dummy vA
dEq_T = dummy (appEq vT)

-- Applications
eq_Id = eapp1 ceq eId

-- Convenience functions
eapp1 fe ae1 = SApp fe [] ae1
eapp2 fe ae1 ae2 = eapp1 (eapp1 fe ae1) ae2

elam1 n1 e = SLam [] n1 e
elam2 n1 n2 e = elam1 n1 (elam1 n2 e)

appEq = eapp1 cEq
dummy = SBind "£"

funTSet = SFun [bTSet]
funASet = SFun [bASet]
fun = SFun []

