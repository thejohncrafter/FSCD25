module Syntax where

data Con : Set
data Ty  : Con → Set
data Var : Con → Set
data Tm  : Con → Set

data Con where
  ⊥ : Con
  _,_ : (Γ : Con) → Ty Γ → Con

data Ty where
  U  : {Γ : Con} → Ty Γ
  Pi : {Γ : Con} → (A : Ty Γ) → (F : Ty (Γ , A)) → Ty Γ
  El : {Γ : Con} → Tm Γ → Ty Γ

data Var where
  here
    : {Γ : Con}
    → (A : Ty Γ)
    → Var (Γ , A)
  there
    : {Γ : Con} → {T : Ty Γ}
    → Var Γ
    → Var (Γ , T)

data Tm where
  var : {Γ : Con} → Var Γ → Tm Γ
  lam
    : {Γ : Con}
    → (A : Ty Γ) → (F : Ty (Γ , A))
    → Tm (Γ , A)
    → Tm Γ
  app
    : {Γ : Con}
    → (A : Ty Γ) → (F : Ty (Γ , A))
    → Tm Γ → Tm Γ
    → Tm Γ

infixl 15 _,_

record Substitution (Op : Con → Con → Set) (F G : Con → Set) : Set₁ where
  field
    _[_] : {Γ Δ : Con} → F Δ → Op Γ Δ → G Γ

open Substitution {{...}} public
