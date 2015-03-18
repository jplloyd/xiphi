module AVec where

-- Natural numbers and dependent vectors
postulate
  Nat : Set
  zero : Nat
  suc  : Nat -> Nat

  Vec : Set -> Nat -> Set
  vnil : (A : Set) -> Vec A zero

-- Some possible type definitions for vcons with different ordering of implicits.
vconsT = {A : Set} {n : Nat} -> A ->              Vec A n -> Vec A (suc n)
vflipT = {n : Nat} {A : Set} -> A ->              Vec A n -> Vec A (suc n)
vskipT = {A : Set}           -> A -> {n : Nat} -> Vec A n -> Vec A (suc n)

-- Choose vconsT as standard vcons type
postulate  
  vcons : vconsT

-- First group of implicits may be permuted back and forth in simple synonyms
vflip : vflipT
vflip = vcons
-- vflip = \{n} {A} -> vcons {_} {_}

vflop : vconsT
vflop = vflip
-- vflop = \{A} {n} -> vflip {_} {_}

-- An implicit arg may skip over an explicit arg in any direction.
vskip : vskipT
vskip = \    a     -> vcons         a
-- vskip = \{A} a {n} -> vcons {_} {_} a

vskop : vconsT
vskop = \        a -> vskip     a
-- vskop = \{A} {n} a -> vskip {_} a {_}

-- For Xiphi-compatible versions, add one extra explicit binding to the lambda,
-- along with corresponding application in body.
