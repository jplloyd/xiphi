module CalcLamSol where

import Internal
import Types

--------------- Eq ---------------

--Eq : (r₀ : sig{A : Set}) → (v₀ : r₀.A) → (r₁ : sig{}) → (v₁ : r₀.A) → Set

_EqType = IFun (V RecBind 0,ISig [IBind {ibF = "A", ibTerm = ISet}]) (IFun (V VarBind 0,IProj (IVar (V RecBind 0)) "A") (IFun (V RecBind 1,ISig []) (IFun (V VarBind 1,IProj (IVar (V RecBind 0)) "A") ISet)))


-------------- refl --------------

--refl : (r₂ : sig{B : Set}) → (v₂ : r₂.B) → <Eq> _2 _3 _6 _7

reflType = IFun (V RecBind 2,ISig [IBind {ibF = "B", ibTerm = ISet}]) (IFun (V VarBind 2,IProj (IVar (V RecBind 2)) "B") (IApp (IApp (IApp (IApp (ICns "Eq") _2) _3) _6) _7))

_2 = IStruct [Ass {assF = "A", assTerm = goProj}]
_3 = IVar (V VarBind 2)
_6 = IStruct []
_7 = IVar (V VarBind 2)
-- where
goProj = IProj (IVar (V RecBind 2)) "B"

{-
_0 <- sig{A : Set}
_1 <- struct{A := _X}
_X <- r₂.B
_2 <- _1
_3 <- v₂
_4 <- sig{}
_5 <- struct{}
_6 <- _5
_7 <- v₂
-}


--------------- w ---------------

--w : (r₃ : sig{}) → (v₃ : (r₄ : sig{}) → (v₄ : Set) → (r₅ : sig{}) → (v₅ : Set) → Set) → (r₆ : sig{}) → (v₆ : <Eq> _10 _11 _14 _19) → (r₉ : sig{}) → (v₉ : v₃ _22 (r₁₀ : sig{A : Set}) → (v₁₀ : r₁₀.A) → r₁₀.A _25 (r₁₁ : sig{}) → (v₁₁ : Set) → Set) → Set

wType = IFun (V RecBind 3,ISig []) (IFun (V VarBind 3,IFun (V RecBind 4,ISig []) (IFun (V VarBind 4,ISet) (IFun (V RecBind 5,ISig []) (IFun (V VarBind 5,ISet) ISet)))) (IFun (V RecBind 6,ISig []) (IFun (V VarBind 6,IApp (IApp (IApp (IApp (ICns "Eq") _10) _11) _14) _19) (IFun (V RecBind 9,ISig []) (IFun (V VarBind 9,IApp (IApp (IApp (IApp (IVar (V VarBind 3)) _22) (IFun (V RecBind 10,ISig [IBind {ibF = "A", ibTerm = ISet}]) (IFun (V VarBind 10,IProj (IVar (V RecBind 10)) "A") (IProj (IVar (V RecBind 10)) "A")))) _25) (IFun (V RecBind 11,ISig []) (IFun (V VarBind 11,ISet) ISet))) ISet)))))

_10 = IStruct [Ass {assF = "A", assTerm = _Y}]
_11 = IVar (V VarBind 3)
_14 = IStruct []
_19 = fatLamw
_22 = IStruct []
_25 = IStruct []
--where
_Y = IFun (V RecBind 4,ISig [])
     (IFun (V VarBind 4,ISet)
      (IFun (V RecBind 5,ISig [])
       (IFun (V VarBind 5,ISet) 
         ISet)))
fatLamw = ILam (V RecBind 7,ISig [])
          (ILam (V VarBind 7,ISet)
           (ILam (V RecBind 8,ISig [])
            (ILam (V VarBind 8,ISet) $
              IVar (V VarBind 7))))

{-
_8 <- sig{A : Set}
_9 <- struct{A := _Y}
_Y <- (r₄ : sig{}) → (v₄ : Set) → (r₅ : sig{}) → (v₅ : Set) → Set
_10<- _9
_11<- v₃
_12<- sig{}
_13<- struct
_14<- _13
_15<- sig{}
_16<- Set
_17<- sig{}
_18<- Set
_19<- \(r₇ : sig{}) → \(v₇ : Set) → \(r₈ : sig{}) → \(v₈ : Set) → v₇
_20<- sig{}
_21<- struct{}
_22<- _21
_23<- sig{}
_24<- struct{}
_25<- _24
-}


--------------- f ---------------

--f : (r₁₂ : sig{}) → (v₁₂ : (r₁₃ : sig{}) → (v₁₃ : Set) → (r₁₄ : sig{}) → (v₁₄ : Set) → Set) → (r₁₅ : sig{}) → (v₁₅ : v₁₂ _28 (r₁₆ : sig{A : Set}) → (v₁₆ : r₁₆.A) → r₁₆.A _31 (r₁₇ : sig{}) → (v₁₇ : Set) → Set) → (r₁₈ : sig{}) → (v₁₈ : <Eq> _34 _35 _38 _43) → Set

fType = IFun (V RecBind 12,ISig []) (IFun (V VarBind 12,IFun (V RecBind 13,ISig []) (IFun (V VarBind 13,ISet) (IFun (V RecBind 14,ISig []) (IFun (V VarBind 14,ISet) ISet)))) (IFun (V RecBind 15,ISig []) (IFun (V VarBind 15,IApp (IApp (IApp (IApp (IVar (V VarBind 12)) _28) (IFun (V RecBind 16,ISig [IBind {ibF = "A", ibTerm = ISet}]) (IFun (V VarBind 16,IProj (IVar (V RecBind 16)) "A") (IProj (IVar (V RecBind 16)) "A")))) _31) (IFun (V RecBind 17,ISig []) (IFun (V VarBind 17,ISet) ISet))) (IFun (V RecBind 18,ISig []) (IFun (V VarBind 18,IApp (IApp (IApp (IApp (ICns "Eq") _34) _35) _38) _43) ISet)))))

_28 = IStruct []
_31 = IStruct []
_34 = IStruct [Ass {assF = "A", assTerm = _Z}]
_35 = IVar (V VarBind 3)
_38 = IStruct []
_43 = fatLamf
--where
_Z = IFun (V RecBind 13,ISig [])
     (IFun (V VarBind 13,ISet)
      (IFun (V RecBind 14,ISig [])
       (IFun (V VarBind 14,ISet) 
         ISet)))
fatLamf = ILam (V RecBind 19,ISig [])
          (ILam (V VarBind 19,ISet)
           (ILam (V RecBind 20,ISig [])
            (ILam (V VarBind 20,ISet) $
              IVar (V VarBind 19))))

{-
_26<- sig{}
_27<- struct{}
_28<- _27
_29<- sig{}
_30<- struct{}
_31<- _30
_32<- sig{A : Set}
_33<- struct{A := _Z}
_Z <- (r₁₃ : sig{}) → (v₁₃ : Set) → (r₁₄ : sig{}) → (v₁₄ : Set) → Set
_34<- _33
_35<- v₁₂
_36<- sig{}
_37<- struct{}
_38<- _37
_39<- sig{}
_40<- Set
_41<- sig{}
_42<- Set
_43<- \(r₁₉ : sig{}) → \(v₁₉ : Set) → \(r₂₀ : sig{}) → \(v₂₀ : Set) → v₁₉
-}
