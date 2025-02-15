module Wkn where

open import Syntax

data Wkn : Con → Con → Set
wkn-ty  : {Γ Δ : Con} → Ty  Δ → Wkn Γ Δ → Ty  Γ
wkn-var : {Γ Δ : Con} → Var Δ → Wkn Γ Δ → Var Γ
wkn-tm  : {Γ Δ : Con} → Tm  Δ → Wkn Γ Δ → Tm  Γ

data Wkn where
  wkn : {Γ : Con} → (A : Ty Γ) → Wkn (Γ , A) Γ
  _↑_
    : {Γ Δ : Con} → (σ : Wkn Γ Δ)
    → (A : Ty Δ)
    → Wkn (Γ , wkn-ty A σ) (Δ , A)

infixl 20 _↑_

wkn-ty U        σ = U
wkn-ty (Pi A B) σ = Pi (wkn-ty A σ) (wkn-ty B (σ ↑ A))
wkn-ty (El t)   σ = El (wkn-tm t σ)

wkn-var v         (wkn A) = there v
wkn-var (here A)  (σ ↑ B) = here _
wkn-var (there v) (σ ↑ B) = there (wkn-var v σ)

wkn-tm (var v)     σ = var (wkn-var v σ)
wkn-tm (lam A F f)   σ = lam (wkn-ty A σ) (wkn-ty F (σ ↑ A)) (wkn-tm f (σ ↑ A))
wkn-tm (app A F f x) σ = app (wkn-ty A σ) (wkn-ty F (σ ↑ A)) (wkn-tm f σ) (wkn-tm x σ)

instance
  wkn-ty-op : Substitution Wkn Ty Ty
  wkn-ty-op = record { _[_] = wkn-ty }
  wkn-var-op : Substitution Wkn Var Var
  wkn-var-op = record { _[_] = wkn-var }
  wkn-tm-op : Substitution Wkn Tm Tm
  wkn-tm-op = record { _[_] = wkn-tm }

{-# DISPLAY wkn-ty A σ = A [ σ ] #-}
{-# DISPLAY wkn-var v σ = v [ σ ] #-}
{-# DISPLAY wkn-tm t σ = t [ σ ] #-}
