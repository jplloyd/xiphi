module ATy where

Ty = {T : Set -> Set} -> ({A : Set} -> T A -> Set) -> Set

postulate
  f : Ty

worksAgda : Ty
worksAgda = f
-- => elaborates to =>
solvableAgda : Ty
solvableAgda = λ {T} -> f {_}

--failsAgda : Ty
--failsAgda = λ g -> f g
-- => elaborates to =>
--unsolvableAgda : Ty
--unsolvableAgda = λ {T} g -> f {_} (λ {A} -> g {_})

giveT : Ty
giveT = λ {T} g -> f {T} (λ {A} -> g {_})

giveA : Ty
giveA = λ {T} g -> f {_} (λ {A} -> g {A})



-- Xiphi-compatible versions

-- Ty = {T : (_ : Set) -> Set} -> 
--      (_ : {A : Set} -> (_ : T A) -> Set) -> 
--        Set

-- postulate
--   f : Ty

-- works : Ty
-- works = f

-- solva : Ty
-- solva = λ {T} g -> f {_} g
-- solva = λ     g -> f     g
-- solva = failsAgda

-- unsol : Ty
-- unsol = λ {T} g -> f {_} (λ {A} ta -> g {_} ta)
-- unsol = λ     g -> f     (λ     ta -> g     ta)

-- giveT : Ty
-- giveT = λ {T} g -> f {T} (λ {A} ta -> g {_} ta)
-- giveT = λ {T} g -> f {T} (λ     ta -> g     ta)

-- giveA : Ty
-- giveA = λ {T} g -> f {_} (λ {A} ta -> g {A} ta)
-- giveA = λ     g -> f     (λ {A} ta -> g {A} ta)
