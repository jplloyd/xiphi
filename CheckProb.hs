

-- Imports

import Surface
import qualified Core as C
import qualified Internal as I
import ScopeCheck
import Elaboration

import Internal(liftG)


import Control.Monad.Trans.Reader
import Control.Monad.Trans.State


data ChkProb = ChkProb [(N,Expr)] Expr Expr


-- Check a problem given a set of postulates and a single type checking problem
-- A Type checking problem consists of a set of postulates followed by two expressions, the
-- first to be checked against the second.
--checkProb :: ChkProb -> Maybe (I.Xi,a)
checkProb (ChkProb posts e eT) = do
  consts <- scopecheckPostulates emptyC (SS posts)
  e' <- scopecheck emptyC e -- > Turn into core
  eT' <- scopecheck emptyC eT
  let elab = do
        elabSigma consts -- cs <-     -- elaborate the postulates into constants (with approriate scoping)
--        tT <- local (liftG (++cs)) (check (I.Gamma []) eT' I.Set)
--        local (liftG (++cs)) (check (I.Gamma []) e' tT)
  let (term, xi) = runState (runReaderT elab (I.Gamma [])) I.emptyXi
  return (xi,term) -- $ elaborate iConsts e' tT
-- Run the evaluation and obsolete

-- Consider using Either for some improved error messages

-- Encoded problems - the lambda example
eBool = fun dSet (fun dSet Set)
etrue = elam2 _x _y vx

epoly = funASet dA vA
emono = fun dSet Set

-- Postulates
postulate =
  [(_Eq, funASet dA (fun dA Set))
  ,(_refl, funASet aA (appEq va va))
--  ,(_w, fun bbBool (fun dappEq_vb_true (fun difb Set)))
--  ,(_f, fun bbBool (fun difb (fun dappEq_vb_true Set)))
  ]

-- Type checking problems
works = ChkProb postulate (eapp3 cw Wld refl_Wld eid) Set
fails = ChkProb postulate (eapp3 cf Wld eid refl_Wld) Set


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
cEq = Cns _Eq
crefl = Cns _refl
cw = Cns _w
cf = Cns _f

-- Variables
vA = Var _A
va = Var _a
vx = Var _x
vz = Var _z
vb = Var _b

-- Bindings
bASet = Bind _A Set
aA = Bind _a vA
bbBool = Bind _b eBool

-- Dummy bindings
dSet = dummy Set
dA = dummy vA
dappEq_vb_true = dummy (appEq vb etrue)
difb = dummy (eapp2 vb epoly emono)

-- Function abstractions
eid = elam1 _z vz

-- Applications
refl_Wld = eapp1 crefl Wld

-- Convenience functions
eapp1 fe ae1 = App fe [] ae1
eapp2 fe ae1 ae2 = eapp1 (eapp1 fe ae1) ae2
eapp3 fe ae1 ae2 ae3 = eapp1 (eapp2 fe ae1 ae2) ae3

elam1 n1 e = Lam [] n1 e
elam2 n1 n2 e = elam1 n1 (elam1 n2 e)

appEq = eapp2 cEq
dummy = Bind "£"

funASet = Fun [bASet]
fun = Fun []
