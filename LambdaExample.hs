module LambdaExample (works,fails) where

import Surface

eBool = fun dSet (fun dSet SSet)
etrue = elam2 _x _y vx

epoly = funASet dA vA
emono = fun dSet SSet

-- Postulates
postulates =
  [(_Eq, funASet dA (fun dA SSet))
  ,(_refl, funASet baA (appEq va va))
  ,(_w, fun bbBool (fun dappEq_vb_true (fun difb SSet)))
  ,(_f, fun bbBool (fun difb (fun dappEq_vb_true SSet)))
  ]

-- Type checking problems
works = ChkProb postulates (eapp3 cw SWld refl_Wld eid) SSet
fails = ChkProb postulates (eapp3 cf SWld eid refl_Wld) SSet


-- Identifiers
_Eq = "Eq"
_refl = "refl"
_A = "A"
_a = "a"
_w = "w"
_f = "f"
_b = "b"
_x = "x"
_y = "y"
_z = "z"

-- Constants
cEq = SCns _Eq
crefl = SCns _refl
cw = SCns _w
cf = SCns _f

-- Variables
vA = SVar _A
va = SVar _a
vx = SVar _x
vz = SVar _z
vb = SVar _b

-- Bindings
bASet = SBind _A SSet
baA = SBind _a vA
bbBool = SBind _b eBool

-- Dummy bindings
dSet = dummy SSet
dA = dummy vA
dappEq_vb_true = dummy (appEq vb etrue)
difb = dummy (eapp2 vb epoly emono)

-- Function abstractions
eid = elam1 _z vz

-- Applications
refl_Wld = eapp1 crefl SWld

-- Convenience functions
eapp1 fe ae1 = SApp fe [] ae1
eapp2 fe ae1 ae2 = eapp1 (eapp1 fe ae1) ae2
eapp3 fe ae1 ae2 ae3 = eapp1 (eapp2 fe ae1 ae2) ae3

elam1 n1 e = SLam [] n1 e
elam2 n1 n2 e = elam1 n1 (elam1 n2 e)

appEq = eapp2 cEq
dummy = SBind "£"

funASet = SFun [bASet]
fun = SFun []
