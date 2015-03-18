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
linear : Set
linear = w (eq Id) (λ x -> x)

-- Fails because the (λ x -> x) cannot be made polymorphic after the fact
-- nonlin : Set
-- nonlin = f (λ x -> x) (eq Id)


-- An additional observation:

-- Typed polymorphic identity function
id : Id
id = λ {A : Set} (a : A) → a

-- Works since hidden lambda is inserted, as well as hidden argument
lin : Set
lin = w (eq Id) id
-- lin = w (eq Id) (id {_})
-- lin = w (eq Id) (λ {A} -> id {_})

-- Interestingly, the following because of a different, but possibly related issue,
-- namely that a meta is unnecessarily inserted for the implicit argument of id.
-- non : Set
-- non = f  id      (eq Id)
-- non = f (id {_}) (eq Id)
-- This indicates a discrepancy where hidden arguments are inserted more eagerly
-- than hidden lambdas: it type checks a dummy hidden lambda is inserted as well.
-- non = f (λ {A} -> id {_}) (eq Id)
