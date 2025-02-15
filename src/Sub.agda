module Sub where

open import Syntax
open import Wkn

data Sub : Con → Con → Set
sub-ty  : {Γ Δ : Con} → Ty  Δ → Sub Γ Δ → Ty Γ
sub-var : {Γ Δ : Con} → Var Δ → Sub Γ Δ → Tm Γ
sub-tm  : {Γ Δ : Con} → Tm  Δ → Sub Γ Δ → Tm Γ

data Sub where
  sub : {Γ : Con} → {A : Ty Γ} → (t : Tm Γ) → Sub Γ (Γ , A)
  _↑_
    : {Γ Δ : Con} → (σ : Sub Γ Δ)
    → (A : Ty Δ)
    → Sub (Γ , sub-ty A σ) (Δ , A)

infixl 20 _↑_

sub-ty U        σ = U
sub-ty (Pi A B) σ = Pi (sub-ty A σ) (sub-ty B (σ ↑ A))
sub-ty (El t)   σ = El (sub-tm t σ)

sub-var (here A)  (sub t) = t
sub-var (there v) (sub t) = var v
sub-var (here _)  (σ ↑ B) = var (here _)
sub-var (there v) (σ ↑ B) = sub-var v σ [ wkn _ ]

sub-tm (var v)     σ = sub-var v σ
sub-tm (lam A F f)   σ = lam (sub-ty A σ) (sub-ty F (σ ↑ A)) (sub-tm f (σ ↑ A))
sub-tm (app A F f x) σ = app (sub-ty A σ) (sub-ty F (σ ↑ A)) (sub-tm f σ) (sub-tm x σ)

instance
  sub-ty-op : Substitution Sub Ty Ty
  sub-ty-op = record { _[_] = sub-ty }
  sub-var-op : Substitution Sub Var Tm
  sub-var-op = record { _[_] = sub-var }
  sub-tm-op : Substitution Sub Tm Tm
  sub-tm-op = record { _[_] = sub-tm }

{-# DISPLAY sub-ty A σ = A [ σ ] #-}
{-# DISPLAY sub-var v σ = v [ σ ] #-}
{-# DISPLAY sub-tm t σ = t [ σ ] #-}
