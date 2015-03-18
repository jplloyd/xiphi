module AVec where

postulate
  Nat : Set
  zero : Nat
  suc  : (_ : Nat) -> Nat

  Vec : (_ : Set) -> ((_ : Nat) -> Set)
  vnil : (A : Set) -> Vec A zero

origvconstype = {A : Set} -> {n : Nat} -> (_ : A) -> ((_ : Vec A n) -> Vec A (suc n))
flipvconstype = {A : Set} -> (_ : A) -> ({n : Nat} -> (_ : Vec A n) -> Vec A (suc n))

postulate  
  vcons : origvconstype
  vflip : flipvconstype

works : flipvconstype
works = \    a     v -> vcons         a v
--works = \{A} a {n} v -> vcons {_} {_} a v

fails : flipvconstype
fails = \    a     -> vcons         a
--fails = \{A} a {n} -> vcons {_} {_} a

flips : origvconstype
flips = \        a v -> vflip     a     v
--flips = \{A} {n} a v -> vflip {_} a {_} v

flops : origvconstype
flops = \        a -> vflip     a
--flops = \{A} {n} a -> vflip {_} a {_}
