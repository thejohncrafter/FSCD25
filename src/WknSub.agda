module WknSub where

open import Syntax
open import Wkn
open import Sub
open import Extension
open import IdxEq
open import MapHeq

open import UpWkn
open import UpSub

private
  lemma-con
    : (Δ : Con)
    → {B : Con}
    → (T : Ty B) → (x : Tm B)
    → (xt : XT B Δ)
    → xt-sub-con (xt-wkn xt (wkn T)) (sub x)
    ≡ Δ

  lemma-ty
    : {Δ : Con} → (A : Ty Δ)
    → {B : Con}
    → (T : Ty B) → (x : Tm B)
    → (xt : XT B Δ)
    →  A [ xt-wkn-op xt (wkn T) ] [ xt-sub-op (xt-wkn xt (wkn T)) (sub x) ]
    ≡* A

  lemma-var
    : {Δ : Con} → (v : Var Δ)
    → {B : Con}
    → (T : Ty B) → (x : Tm B)
    → (xt : XT B Δ)
    →  v [ xt-wkn-op xt (wkn T) ] [ xt-sub-op (xt-wkn xt (wkn T)) (sub x) ]
    ≡* var v

  lemma-tm
    : {Δ : Con} → (t : Tm Δ)
    → {B : Con}
    → (T : Ty B) → (x : Tm B)
    → (xt : XT B Δ)
    →  t [ xt-wkn-op xt (wkn T) ] [ xt-sub-op (xt-wkn xt (wkn T)) (sub x) ]
    ≡* t

  lemma-con ⊥ T x zero = refl
  lemma-con (Γ , A) T x zero = refl
  lemma-con (Γ , A) T x (succ xt _) = map-heq-cons (lemma-con Γ T x xt) (lemma-ty _ _ _ _)

  lemma-ty U        T x xt = map-heq-U (lemma-con _ T x xt)
  lemma-ty (Pi A F) T x xt = map-heq-Pi (lemma-ty _ _ _ _) (lemma-ty _ _ _ _)
  lemma-ty (El t)   T x xt = map-heq-El (lemma-tm t _ _ _)

  lemma-var (here A)          T x zero        = refl
  lemma-var (here A)          T x (succ xt _) = map-heq-var (map-heq-here (lemma-ty _ _ _ _))
  lemma-var (there v)         T x zero        = refl
  lemma-var (there {_} {S} v) T x (succ xt _) = map-heq-wkn-tm (lemma-tm _ _ _ xt) (lemma-ty _ _ _ _)

  lemma-tm (var v)       T x xt = lemma-var _ _ _ xt
  lemma-tm (lam A F f)   T x xt = map-heq-lam (lemma-ty _ _ _ _) (lemma-ty _ _ _ _) (lemma-tm f _ _ _)
  lemma-tm (app A F f u) T x xt = map-heq-app (lemma-ty _ _ _ _) (lemma-ty _ _ _ _) (lemma-tm f _ _ _) (lemma-tm _ _ _ _)

wkn-sub-ty
  : {Δ : Con} → (A : Ty Δ)
  → (T : Ty Δ) → (x : Tm Δ)
  → A [ wkn T ] [ sub x ] ≡ A
wkn-sub-ty A x T = eq-of-ty-idxeq (lemma-ty A x T zero)

wkn-sub-var
  : {Δ : Con} → (v : Var Δ)
  → (T : Ty Δ) → (t : Tm Δ)
  → v [ wkn T ] [ sub t ] ≡ var v
wkn-sub-var v x T = eq-of-tm-idxeq (lemma-var v x T zero)

wkn-sub-tm
  : {Δ : Con} → (t : Tm Δ)
  → (T : Ty Δ) → (x : Tm Δ)
  → t [ wkn T ] [ sub x ] ≡ t
wkn-sub-tm t x T = eq-of-tm-idxeq (lemma-tm t x T zero)
