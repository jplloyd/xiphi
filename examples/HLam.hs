module HLam (works,fails) where

import Surface
import CheckHub

eBool = fun dSet (fun dSet SSet)
etrue = elam2 _x _y vx

epoly = funASet dA vA
emono = fun dSet SSet

-- Postulates
postulates =
  [(_Eq, funASet dA SSet)
  ,(_eq, funBSet baB (appEq vB va))
  ,(_w, funbBool dappEq_vb (fun difb SSet))
  ,(_f, funbBool difb (fun dappEq_vb SSet))
  ]

-- Type checking problems
simple n = ChkProb (take n postulates) SSet SSet
works = chkSet (eapp2 cw eq_true eid)
fails = chkSet (eapp2 cf eid eq_true)
-- where
chkSet e = ChkProb postulates e SSet

-- Identifiers
_Eq = "Eq"
_eq = "eq"
_A = "A"
_B = "B"
_a = "a"
_w = "w"
_f = "f"
_b = "b"
_x = "x"
_y = "y"
_z = "z"

-- Constants
cEq = SCns _Eq
ceq = SCns _eq
cw = SCns _w
cf = SCns _f

-- Variables
vA = SVar _A
vB = SVar _B
va = SVar _a
vx = SVar _x
vz = SVar _z
vb = SVar _b

-- Bindings
bASet = SBind _A SSet
bBSet = SBind _B SSet
baA = SBind _a vA
baB = SBind _a vB
bbBool = SBind _b eBool

-- Dummy bindings
dSet = dummy SSet
dA = dummy vA
dappEq_vb = dummy (appEq eBool vb)
difb = dummy (eapp2 vb epoly emono)

-- Function abstractions
eid = elam1 _z vz

-- Applications
eq_true = SApp ceq [SPos eBool] etrue

-- Convenience functions
eapp1 fe ae1 = SApp fe [] ae1
eapp2 fe ae1 ae2 = eapp1 (eapp1 fe ae1) ae2

elam1 n1 e = SLam [] n1 e
elam2 n1 n2 e = elam1 n1 (elam1 n2 e)

appEq impl = SApp cEq [SPos impl]
dummy = SBind "£"

funASet = SFun [bASet]
funbBool = SFun [bbBool]
fun = SFun []

funBSet = SFun [bBSet]
