module Extension where

open import Syntax
open import Wkn
open import Sub

data XT : Con → Con → Set

data XT where
  zero : {B : Con} → XT B B
  succ : {B Δ : Con} → XT B Δ → (A : Ty Δ) → XT B (Δ , A)

xt-wkn-con : {A B Δ : Con} → (xt : XT B Δ) → (σ : Wkn A B) → Con
xt-wkn-op  : {A B Δ : Con} → (xt : XT B Δ) → (σ : Wkn A B) → Wkn (xt-wkn-con xt σ) Δ
xt-wkn     : {A B Δ : Con} → (xt : XT B Δ) → (σ : Wkn A B) → XT A (xt-wkn-con xt σ)

xt-wkn-con {A} {B} {Δ} zero       σ = A
xt-wkn-con {A} {B} {Δ} (succ e T) σ = xt-wkn-con e σ , wkn-ty T (xt-wkn-op e σ)

xt-wkn-op              zero σ = σ
xt-wkn-op              (succ e T) σ = xt-wkn-op e σ ↑ T

xt-wkn                 zero       σ = zero
xt-wkn                 (succ e T) σ = succ (xt-wkn e σ) (wkn-ty T (xt-wkn-op e σ))

xt-sub-con : {A B Δ : Con} → (xt : XT B Δ) → (σ : Sub A B) → Con
xt-sub-op  : {A B Δ : Con} → (xt : XT B Δ) → (σ : Sub A B) → Sub (xt-sub-con xt σ) Δ
xt-sub     : {A B Δ : Con} → (xt : XT B Δ) → (σ : Sub A B) → XT A (xt-sub-con xt σ)

xt-sub-con {A} {B} {Δ} zero       σ = A
xt-sub-con {A} {B} {Δ} (succ e T) σ = xt-sub-con e σ , sub-ty T (xt-sub-op e σ)

xt-sub-op              zero σ = σ
xt-sub-op              (succ e T) σ = xt-sub-op e σ ↑ T

xt-sub                 zero       σ = zero
xt-sub                 (succ e T) σ = succ (xt-sub e σ) (sub-ty T (xt-sub-op e σ))
