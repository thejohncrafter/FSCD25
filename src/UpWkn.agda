module UpWkn where

open import Syntax
open import Wkn
open import Sub
open import Extension
open import IdxEq
open import MapHeq

private
  lemma-con
    : (Δ : Con)
    → {B' B : Con} → (σ : Wkn B' B)
    → (T : Ty B)
    → (xt : XT B Δ)
    → xt-wkn-con (xt-wkn xt (wkn T)) (σ ↑ T)
    ≡ xt-wkn-con (xt-wkn xt σ      ) (wkn (T [ σ ]))

  lemma-ty
    : {Δ : Con} → (A : Ty Δ)
    → {B' B : Con} → (σ : Wkn B' B)
    → (T : Ty B)
    → (xt : XT B Δ)
    →  A [ xt-wkn-op xt (wkn T) ] [ xt-wkn-op (xt-wkn xt (wkn T)) (σ ↑ T) ]
    ≡* A [ xt-wkn-op xt σ       ] [ xt-wkn-op (xt-wkn xt σ) (wkn (T [ σ ])) ]

  lemma-var
    : {Δ : Con} → (v : Var Δ)
    → {B' B : Con} → (σ : Wkn B' B)
    → (T : Ty B)
    → (xt : XT B Δ)
    →  v [ xt-wkn-op xt (wkn T) ] [ xt-wkn-op (xt-wkn xt (wkn T)) (σ ↑ T) ]
    ≡* v [ xt-wkn-op xt σ       ] [ xt-wkn-op (xt-wkn xt σ) (wkn (T [ σ ])) ]

  lemma-tm
    : {Δ : Con} → (t : Tm Δ)
    → {B' B : Con} → (σ : Wkn B' B)
    → (T : Ty B)
    → (xt : XT B Δ)
    →  t [ xt-wkn-op xt (wkn T) ] [ xt-wkn-op (xt-wkn xt (wkn T)) (σ ↑ T) ]
    ≡* t [ xt-wkn-op xt σ       ] [ xt-wkn-op (xt-wkn xt σ) (wkn (T [ σ ])) ]

  lemma-con ⊥ σ T zero = refl
  lemma-con (Γ , A) σ T zero = refl
  lemma-con (Γ , A) σ T (succ xt _) = map-heq-cons (lemma-con _ _ _ _) (lemma-ty _ _ _ _)

  lemma-ty U        σ T xt = map-heq-U (lemma-con _ _ _ _)
  lemma-ty (Pi A F) σ T xt = map-heq-Pi (lemma-ty _ _ _ _) (lemma-ty _ _ _ _)
  lemma-ty (El t)   σ T xt = map-heq-El (lemma-tm _ _ _ _)

  lemma-var (here A)  σ T zero       = refl
  lemma-var (here A)  σ T (succ e _) = map-heq-here (lemma-ty _ _ _ _)
  lemma-var (there v) σ T zero       = refl
  lemma-var (there v) σ T (succ e _) = map-heq-there (lemma-ty _ _ _ _) (lemma-var _ _ _ _)

  lemma-tm (var v)       σ T xt = map-heq-var (lemma-var _ _ _ _)
  lemma-tm (lam A F f)   σ T xt = map-heq-lam (lemma-ty _ _ _ _) (lemma-ty _ _ _ _) (lemma-tm _ _ _ _)
  lemma-tm (app A F f x) σ T xt = map-heq-app (lemma-ty _ _ _ _) (lemma-ty _ _ _ _) (lemma-tm _ _ _ _) (lemma-tm _ _ _ _)

up-wkn-ty
  : {Δ : Con} → (A : Ty Δ)
  → {Γ : Con} → (σ : Wkn Γ Δ)
  → (T : Ty Δ)
  → A [ wkn T ] [ σ ↑ T ] ≡ A [ σ ] [ wkn (T [ σ ]) ]
up-wkn-ty A σ T = eq-of-ty-idxeq (lemma-ty _ _ _ zero)

up-wkn-var
  : {Δ : Con} → (v : Var Δ)
  → {Γ : Con} → (σ : Wkn Γ Δ)
  → (T : Ty Δ)
  → v [ wkn T ] [ σ ↑ T ] ≡ v [ σ ] [ wkn (T [ σ ]) ]
up-wkn-var v σ T = eq-of-var-idxeq (lemma-var _ _ _ zero)

up-wkn-tm
  : {Δ : Con} → (t : Tm Δ)
  → {Γ : Con} → (σ : Wkn Γ Δ)
  → (T : Ty Δ)
  → t [ wkn T ] [ σ ↑ T ] ≡ t [ σ ] [ wkn (T [ σ ]) ]
up-wkn-tm t σ T = eq-of-tm-idxeq (lemma-tm _ _ _ zero)

up-wkn-ty-1
  : {Δ : Con} → (T₁ : Ty Δ) → (A : Ty (Δ , T₁))
  → {Γ : Con} → (σ : Wkn Γ Δ)
  → (T : Ty Δ)
  →  A [ wkn T ↑ T₁ ] [ σ ↑ T ↑ (T₁ [ wkn T ]) ]
  ≡* A [ σ ↑ T₁ ] [ wkn (T [ σ ]) ↑ (T₁ [ σ ]) ]
up-wkn-ty-1 T₁ A σ T = lemma-ty _ _ _ (succ zero T₁)
