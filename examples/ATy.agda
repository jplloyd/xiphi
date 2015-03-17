module ATy where

Ty = {T : (_ : Set1) -> Set} -> 
     (_ : {b : Set1} -> (_ : T b) -> Set) -> 
       Set

postulate
  f : Ty

works : Ty
works = f

fails : Ty
fails = λ g -> f g

failz : Ty
failz = λ {T} g -> f (\{b} t -> g t)

failc : Ty
failc = λ {T} g -> f {_} (\{b} t -> g {_} t)

hacks : Ty
hacks = λ g -> f (λ {b} -> (λ t -> g {b} t))

hackz : Ty
hackz = λ {T} g -> f {T} g
