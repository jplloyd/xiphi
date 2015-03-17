module ALam where

Bool = (_ : Set1) -> ((_ : Set1) -> Set1)

true : Bool
true = λ x y → x

poly = {A : Set} (_ : A) → A
mono = (_ : Set) → Set

postulate
  Eq : {A : Set2} (_ : A) → Set2
  eq : {B : Set2} (a : B) → (Eq {B} a)
  w : {b : Bool} (_ : Eq b) → ((_ : b poly mono) → Set)
  f : {b : Bool} (_ : b poly mono) → ((_ : Eq b) → Set)

works : Set
works = w (eq {Bool} true) (λ z → z)

--fails : Set
--fails = f (λ z → z) (eq {Bool} true)
