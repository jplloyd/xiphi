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
works = \a v -> vcons a v

fails : flipvconstype
fails = \a -> vcons a

flips : origvconstype
flips = \a v -> vflip a v

flops : origvconstype
flops = \a -> vflip a
