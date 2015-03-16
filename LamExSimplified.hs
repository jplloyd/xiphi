module LamExSimplified (works,fails) where

import Surface
import CheckHub
import CalcLamSol
import Internal
import Types
import Util

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
works = ChkProb postulates worksDef SSet
fails = ChkProb postulates failsDef SSet

worksDef = (eapp2 cw eq_true eid)

failsDef = (eapp2 cf eid eq_true)

postTypes = [_EqT, eqT, wT, fT]

opt def = OCP (maybezipR postulates postTypes) def (SSet,Nothing)

worksOpt = opt worksDef

failsOpt = opt failsDef


_EqT = IFun (V RecBind 0,ISig [IBind {ibF = "A", ibTerm = ISet}]) (IFun (V VarBind 0,IProj (IVar (V RecBind 0)) "A") ISet)

eqT = IFun (V RecBind 1,ISig [IBind {ibF = "B", ibTerm = ISet}]) (IFun (V VarBind 1,IProj (IVar (V RecBind 1)) "B") (IApp (IApp (ICns "Eq") (IStruct [Ass {assF = "A", assTerm = IProj (IVar (V RecBind 1)) "B"}])) (IVar (V VarBind 1))))

wT = IFun (V RecBind 4,ISig [IBind {ibF = "b", ibTerm = IFun (V RecBind 2,ISig []) (IFun (V VarBind 2,ISet) (IFun (V RecBind 3,ISig []) (IFun (V VarBind 3,ISet) ISet)))}]) (IFun (V VarBind 4,IApp (IApp (ICns "Eq") (IStruct [Ass {assF = "A", assTerm = IFun (V RecBind 2,ISig []) (IFun (V VarBind 2,ISet) (IFun (V RecBind 3,ISig []) (IFun (V VarBind 3,ISet) ISet)))}])) (IProj (IVar (V RecBind 4)) "b")) (IFun (V RecBind 5,ISig []) (IFun (V VarBind 5,IApp (IApp (IApp (IApp (IProj (IVar (V RecBind 4)) "b") (IStruct [])) (IFun (V RecBind 6,ISig [IBind {ibF = "A", ibTerm = ISet}]) (IFun (V VarBind 6,IProj (IVar (V RecBind 6)) "A") (IProj (IVar (V RecBind 6)) "A")))) (IStruct [])) (IFun (V RecBind 7,ISig []) (IFun (V VarBind 7,ISet) ISet))) ISet)))

fT = IFun (V RecBind 10,ISig [IBind {ibF = "b", ibTerm = IFun (V RecBind 8,ISig []) (IFun (V VarBind 8,ISet) (IFun (V RecBind 9,ISig []) (IFun (V VarBind 9,ISet) ISet)))}]) (IFun (V VarBind 10,IApp (IApp (IApp (IApp (IProj (IVar (V RecBind 10)) "b") (IStruct [])) (IFun (V RecBind 11,ISig [IBind {ibF = "A", ibTerm = ISet}]) (IFun (V VarBind 11,IProj (IVar (V RecBind 11)) "A") (IProj (IVar (V RecBind 11)) "A")))) (IStruct [])) (IFun (V RecBind 12,ISig []) (IFun (V VarBind 12,ISet) ISet))) (IFun (V RecBind 13,ISig []) (IFun (V VarBind 13,IApp (IApp (ICns "Eq") (IStruct [Ass {assF = "A", assTerm = IFun (V RecBind 8,ISig []) (IFun (V VarBind 8,ISet) (IFun (V RecBind 9,ISig []) (IFun (V VarBind 9,ISet) ISet)))}])) (IProj (IVar (V RecBind 10)) "b")) ISet)))



-- Identifiers
_Eq = "Eq"
_eq = "eq"
_works = "works"
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
