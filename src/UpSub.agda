module UpSub where

open import Syntax
open import Wkn
open import Sub
open import Extension
open import IdxEq
open import MapHeq

open import UpWkn

private
  lemma-con
    : (Δ : Con)
    → {B' B : Con} → (σ : Sub B' B)
    → (T : Ty B)
    → (xt : XT B Δ)
    → xt-sub-con (xt-wkn xt (wkn T)) (σ ↑ T)
    ≡ xt-wkn-con (xt-sub xt σ      ) (wkn (T [ σ ]))

  lemma-ty
    : {Δ : Con} → (A : Ty Δ)
    → {B' B : Con} → (σ : Sub B' B)
    → (T : Ty B)
    → (xt : XT B Δ)
    →   A [ xt-wkn-op xt (wkn T) ] [ xt-sub-op (xt-wkn xt (wkn T)) (σ ↑ T) ]
    ≡* A [ xt-sub-op xt σ       ] [ xt-wkn-op (xt-sub xt σ) (wkn (T [ σ ])) ]

  lemma-var
    : {Δ : Con} → (v : Var Δ)
    → {B' B : Con} → (σ : Sub B' B)
    → (T : Ty B)
    → (xt : XT B Δ)
    →   v [ xt-wkn-op xt (wkn T) ] [ xt-sub-op (xt-wkn xt (wkn T)) (σ ↑ T) ]
    ≡* v [ xt-sub-op xt σ       ] [ xt-wkn-op (xt-sub xt σ) (wkn (T [ σ ])) ]

  lemma-tm
    : {Δ : Con} → (t : Tm Δ)
    → {B' B : Con} → (σ : Sub B' B)
    → (T : Ty B)
    → (xt : XT B Δ)
    →   t [ xt-wkn-op xt (wkn T) ] [ xt-sub-op (xt-wkn xt (wkn T)) (σ ↑ T) ]
    ≡* t [ xt-sub-op xt σ       ] [ xt-wkn-op (xt-sub xt σ) (wkn (T [ σ ])) ]

  lemma-con ⊥ σ T zero = refl
  lemma-con (Γ , A) σ T zero = refl
  lemma-con (Γ , A) σ T (succ xt _) = map-heq-cons (lemma-con _ _ _ _) (lemma-ty _ _ _ _)

  lemma-ty U        σ T xt = map-heq-U (lemma-con _ _ _ _)
  lemma-ty (Pi A F) σ T xt = map-heq-Pi (lemma-ty _ _ _ _) (lemma-ty _ _ _ _)
  lemma-ty (El t)   σ T xt = map-heq-El (lemma-tm t _ _ _)

  lemma-var (here A)      σ T zero       = refl
  lemma-var (here A)      σ T (succ xt _) = map-heq-var (map-heq-here (lemma-ty _ _ _ _))
  lemma-var (there v) σ T zero       = refl
  lemma-var (there {_} {S} v) σ T (succ xt _) =
    begin
        v [ xt-wkn-op xt (wkn T) ] [ wkn (S [ xt-wkn-op xt (wkn T) ]) ] [ xt-sub-op (xt-wkn xt (wkn T)) (σ ↑ T)   ↑ _ ]
      ≡*⟨ refl ⟩
        v [ xt-wkn-op xt (wkn T) ] [ xt-sub-op (xt-wkn xt (wkn T)) (σ ↑ T)   ] [ wkn (S [ xt-wkn-op xt (wkn T) ] [ xt-sub-op (xt-wkn xt (wkn T)) (σ ↑ T)         ]) ]
      ≡*⟨ map-heq-wkn-tm (lemma-var _ _ _ _) (lemma-ty _ _ _ _) ⟩
        v [ xt-sub-op xt σ       ] [ xt-wkn-op (xt-sub xt σ) (wkn (T [ σ ])) ] [ wkn (S [ xt-sub-op xt σ       ] [ xt-wkn-op (xt-sub xt σ      ) (wkn (T [ σ ])) ]) ]
      ≡*⟨ symmetric (≡*-of-eq ((up-wkn-tm _ _ _))) ⟩
        v [ xt-sub-op xt σ       ] [ wkn (S [ xt-sub-op xt σ       ]) ] [ xt-wkn-op (xt-sub xt σ) (wkn (T [ σ ])) ↑ _ ]
    ∎

  lemma-tm (var v)     σ T xt = lemma-var _ _ _ _
  lemma-tm (lam A F f)   σ T xt = map-heq-lam (lemma-ty _ _ _ _) (lemma-ty _ _ _ _) (lemma-tm f _ _ _)
  lemma-tm (app A F f x) σ T xt = map-heq-app (lemma-ty _ _ _ _) (lemma-ty _ _ _ _) (lemma-tm f _ _ _) (lemma-tm x _ _ _)

up-sub-ty
  : {Δ : Con} → (A : Ty Δ)
  → {Γ : Con} → (σ : Sub Γ Δ)
  → (T : Ty Δ)
  → A [ wkn T ] [ σ ↑ T ] ≡ A [ σ ] [ wkn (T [ σ ]) ]
up-sub-ty t σ T = eq-of-ty-idxeq (lemma-ty _ _ _ zero)

up-sub-var
  : {Δ : Con} → (v : Var Δ)
  → {Γ : Con} → (σ : Sub Γ Δ)
  → (T : Ty Δ)
  → v [ wkn T ] [ σ ↑ T ] ≡ v [ σ ] [ wkn (T [ σ ]) ]
up-sub-var v σ T = eq-of-tm-idxeq (lemma-var v _ _ zero)

up-sub-tm
  : {Δ : Con} → (t : Tm Δ)
  → {Γ : Con} → (σ : Sub Γ Δ)
  → (T : Ty Δ)
  → t [ wkn T ] [ σ ↑ T ] ≡ t [ σ ] [ wkn (T [ σ ]) ]
up-sub-tm t σ T = eq-of-tm-idxeq (lemma-tm t _ _ zero)

up-sub-ty-1
  : {Δ : Con} → (T₁ : Ty Δ) → (A : Ty (Δ , T₁))
  → {Γ : Con} → (σ : Sub Γ Δ)
  → (T : Ty Δ)
  →  A [ wkn T ↑ T₁ ] [ σ ↑ T ↑ (T₁ [ wkn T ]) ]
  ≡* A [ σ ↑ T₁ ] [ wkn (T [ σ ]) ↑ (T₁ [ σ ]) ]
up-sub-ty-1 T₁ A σ T = lemma-ty _ _ _ (succ zero T₁)
