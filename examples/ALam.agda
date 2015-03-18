module ALam where

-- Type and value constructors for equivalence classes
postulate
  Eq : Set1 → Set1
  eq : (T : Set1) → Eq T

  w : {T : Set1} → Eq T → T    → Set
  f : {T : Set1} → T    → Eq T → Set

-- Type of polymorphic identity function in Set1
Id : Set1
Id = {A : Set} → A → A

-- Works because (λ x -> x) is made polymorphic using information from (eq Id)
works : Set
works = w (eq Id) (λ x -> x)

-- Fails because the (λ x -> x) cannot be made polymorphic after the fact
-- fails : Set
-- fails = f (λ x -> x) (eq Id)




-- An additional observation:

-- Polymorphic identity function
id : {A : Set} → A → A
id = λ {A : Set} (a : A) → a

-- Works since 
ws : Set
--ws = w (eq Id) id
ws = w (eq Id) (id {_})

-- Interestingly, fs fails because of a different, but possibly related issue,
-- namely that a meta is unnecessarily inserted for the implicit argument of id.
-- fs : Set
-- fs = f  id      (eq Id)
-- fs = f (id {_}) (eq Id)
-- This indicates a discrepancy where hidden arguments are inserted more eagerly
-- than hidden lambdas: fs type checks when the hidden lambda is inserted as well.
-- fs = f (λ {_} -> id {_}) (eq Id)
