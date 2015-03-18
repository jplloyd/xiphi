module HVec where

import Surface
import CheckHub

-- Named expressions
origvconstype = SFun [bASet, bnNat] dA (SFun []      dVAn veccod)
flipvconstype = SFun [bASet]        dA (SFun [bnNat] dVAn veccod)

-- where
veccod = eapp2 cVec vA (eapp1 csuc vn)

-- Postulates
postulate =
  [(_Nat, SSet)
  ,(_zero, cNat)
  ,(_suc, fun dNat cNat)
  
  ,(_Vec, fun dSet (fun dNat SSet))
  ,(_vnil, fun bASet (eapp2 cVec vA czero))

  ,(_vcons, origvconstype)
  ,(_vflip, flipvconstype)
  ]

-- Type checking problems
simple n = ChkProb (take n postulate) (SCns _Nat) SSet
-- Synonym using all arguments still works. Good or bad, who can tell?
works = chkFlip twoArgs
-- Only using the one is doomed to fail.
fails = chkFlip oneArgs
-- Flips
flips = chkOrig twoArgs
-- Flops
flops = chkOrig oneArgs
-- where
chkFlip f = chk (f cvcons) flipvconstype
chkOrig f = chk (f cvflip) origvconstype
twoArgs cv = elam2 _a _v $ eapp2 cv va vv
oneArgs cv = elam1 _a    $ eapp1 cv va
chk exp typ = ChkProb postulate exp typ

-- Identifiers
_Nat   = "Nat"
_zero  = "zero"
_suc   = "suc"
_Vec   = "Vec"
_vnil  = "vnil"
_vcons = "vcons"
_vflip = "vflip"
_A = "A"
_n = "n"
_a = "a"
_v = "v"

-- Constants
cNat   = SCns _Nat
czero  = SCns _zero
csuc   = SCns _suc
cVec   = SCns _Vec
cvnil  = SCns _vnil
cvcons = SCns _vcons
cvflip = SCns _vflip

-- Variables
vA = SVar _A
vn = SVar _n
va = SVar _a
vv = SVar _v

-- Bindings
bASet = SBind _A SSet
bnNat = SBind _n cNat

-- Dummy bindings
dSet = dummy SSet
dNat = dummy cNat
dA   = dummy vA
dVAn = dummy $ eapp2 cVec vA vn

-- Convenience functions
eapp1 fe ae1 = SApp fe [] ae1
eapp2 fe ae1 ae2 = eapp1 (eapp1 fe ae1) ae2

elam1 n1 e = SLam [] n1 e
elam2 n1 n2 e = elam1 n1 (elam1 n2 e)

dummy = SBind "£"

fun = SFun []
