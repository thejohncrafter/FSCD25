module SubSub where

open import Syntax
open import Wkn
open import Sub
open import Extension
open import IdxEq
open import MapHeq

open import UpWkn
open import UpSub
open import WknSub

private
  lemma-con
    : (Δ : Con)
    → {B' B : Con} → (σ : Sub B' B)
    → (T : Ty B) → (x : Tm B)
    → (xt : XT (B , T) Δ)
    → xt-sub-con (xt-sub xt (sub x)) σ
    ≡ xt-sub-con (xt-sub xt (σ ↑ T)) (sub (x [ σ ]))

  lemma-ty
    : {Δ : Con} → (A : Ty Δ)
    → {B' B : Con} → (σ : Sub B' B)
    → (T : Ty B) → (x : Tm B)
    → (xt : XT (B , T) Δ)
    →  A [ xt-sub-op xt (sub x) ] [ xt-sub-op (xt-sub xt (sub x)) σ ]
    ≡* A [ xt-sub-op xt (σ ↑ T) ] [ xt-sub-op (xt-sub xt (σ ↑ T)) (sub (x [ σ ])) ]

  lemma-var
    : {Δ : Con} → (v : Var Δ)
    → {B' B : Con} → (σ : Sub B' B)
    → (T : Ty B) → (x : Tm B)
    → (xt : XT (B , T) Δ)
    →  v [ xt-sub-op xt (sub x) ] [ xt-sub-op (xt-sub xt (sub x)) σ ]
    ≡* v [ xt-sub-op xt (σ ↑ T) ] [ xt-sub-op (xt-sub xt (σ ↑ T)) (sub (x [ σ ])) ]

  lemma-tm
    : {Δ : Con} → (t : Tm Δ)
    → {B' B : Con} → (σ : Sub B' B)
    → (T : Ty B) → (x : Tm B)
    → (xt : XT (B , T) Δ)
    →  t [ xt-sub-op xt (sub x) ] [ xt-sub-op (xt-sub xt (sub x)) σ ]
    ≡* t [ xt-sub-op xt (σ ↑ T) ] [ xt-sub-op (xt-sub xt (σ ↑ T)) (sub (x [ σ ])) ]

  --lemma-con ⊥ σ T x zero = refl
  lemma-con (Γ , A) σ T x zero = refl
  lemma-con (Γ , A) σ T x (succ xt _) = map-heq-cons (lemma-con _ σ _ _ _) (lemma-ty _ σ _ _ _)

  lemma-ty U        σ T x xt = map-heq-U (lemma-con _ σ _ _ _)
  lemma-ty (Pi A F) σ T x xt = map-heq-Pi (lemma-ty _ σ _ _ _) (lemma-ty _ σ _ _ _)
  lemma-ty (El t)   σ T x xt = map-heq-El (lemma-tm t σ _ _ _)

  lemma-var (here A)  σ T x zero       = refl
  lemma-var (here A)  σ T x (succ e _) = map-heq-var (map-heq-here (lemma-ty _ σ _ _ _))
  lemma-var (there v) σ T x zero       =
    begin
      v [ σ ]
      ≡*⟨ symmetric (≡*-of-eq (wkn-sub-tm _ _ _) ) ⟩
      v [ σ ] [ wkn (T [ σ ]) ] [ sub (x [ σ ]) ]
    ∎
  lemma-var (there {_} {S} v) σ T x (succ xt _) =
    begin
        v [ xt-sub-op xt (sub x) ] [ wkn (S [ xt-sub-op xt (sub x) ]) ] [ xt-sub-op (xt-sub xt (sub x)) σ ↑ _ ]
      ≡*⟨ ≡*-of-eq (up-sub-tm ( v [ xt-sub-op xt (sub x) ]) _ _) ⟩
        v [ xt-sub-op xt (sub x) ] [ xt-sub-op (xt-sub xt (sub x)) σ ] [ wkn _ ]
      ≡*⟨ map-heq-wkn-tm (lemma-var v σ _ _ _ ) (lemma-ty _ σ _ _ _) ⟩
        v [ xt-sub-op xt (σ ↑ T) ] [ xt-sub-op (xt-sub xt (σ ↑ T)) (sub (x [ σ ])) ] [ wkn _ ]
      ≡*⟨ symmetric (≡*-of-eq ((up-sub-tm (v [ xt-sub-op xt (σ ↑ T) ]) _ _))) ⟩
        v [ xt-sub-op xt (σ ↑ T) ] [ wkn (S [ xt-sub-op xt (σ ↑ T) ]) ] [ xt-sub-op (xt-sub xt (σ ↑ T)) (sub (x [ σ ])) ↑ _ ]
    ∎

  lemma-tm (var v)       σ T x xt = lemma-var v σ _ _ _
  lemma-tm (lam A F f)   σ T x xt = map-heq-lam (lemma-ty _ σ _ _ _) (lemma-ty _ σ _ _ _) (lemma-tm f _ _ _ _)
  lemma-tm (app A F f u) σ T x xt = map-heq-app (lemma-ty _ σ _ _ _) (lemma-ty _ σ _ _ _) (lemma-tm f _ _ _ _) (lemma-tm u _ _ _ _)

sub-sub-ty
  : {Δ : Con} → (T : Ty Δ) → (A : Ty (Δ , T))
  → {Γ : Con} → (σ : Sub Γ Δ)
  → (x : Tm Δ)
  → A [ sub x ] [ σ ] ≡ A [ σ ↑ T ] [ sub (x [ σ ]) ]
sub-sub-ty T A σ x = eq-of-ty-idxeq (lemma-ty A σ T x zero)

sub-sub-var
  : {Δ : Con} → (T : Ty Δ) → (v : Var (Δ , T))
  → {Γ : Con} → (σ : Sub Γ Δ)
  → (x : Tm Δ)
  → v [ sub x ] [ σ ] ≡ v [ σ ↑ T ] [ sub (x [ σ ]) ]
sub-sub-var T v σ x = eq-of-tm-idxeq (lemma-var v σ T x zero)

sub-sub-tm
  : {Δ : Con} → (T : Ty Δ) → (t : Tm (Δ , T))
  → {Γ : Con} → (σ : Sub Γ Δ)
  → (x : Tm Δ)
  → t [ sub x ] [ σ ] ≡ t [ σ ↑ T ] [ sub (x [ σ ]) ]
sub-sub-tm T t σ x = eq-of-tm-idxeq (lemma-tm t σ T x zero)
