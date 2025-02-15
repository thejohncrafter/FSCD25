module MapHeq where

open import Syntax
open import Wkn
open import Sub
open import IdxEq

map-heq-cons
  : {Γ : Con} → {A : Ty Γ}
  → {Δ : Con} → {B : Ty Δ}
  → Γ ≡ Δ
  → A ≡* B
  → Γ , A ≡ Δ , B
map-heq-cons refl refl = refl

map-heq-U
  : {Γ : Con}
  → {Δ : Con}
  → Γ ≡ Δ
  → U {Γ} ≡* U {Δ}
map-heq-U refl = refl

map-heq-Pi
  : {Γ : Con} → {A : Ty Γ} → {F : Ty (Γ , A)}
  → {Δ : Con} → {B : Ty Δ} → {G : Ty (Δ , B)}
  → A ≡* B
  → F ≡* G
  → Pi A F ≡* Pi B G
map-heq-Pi refl refl = refl

map-heq-El
  : {Γ : Con} → {t : Tm Γ}
  → {Δ : Con} → {u : Tm Δ}
  → t ≡* u
  → El t ≡* El u
map-heq-El refl = refl

map-heq-here
  : {Γ : Con} → {A : Ty Γ}
  → {Δ : Con} → {B : Ty Δ}
  → A ≡*  B
  → here A ≡* here B
map-heq-here refl = refl

map-heq-there
  : {Γ : Con} → {T : Ty Γ} → {v : Var Γ}
  → {Δ : Con} → {U : Ty Δ} → {w : Var Δ}
  → T ≡*  U
  → v ≡* w
  → there {Γ} {T} v ≡* there {Δ} {U} w
map-heq-there refl refl = refl

map-heq-var
  : {Γ : Con} → {v : Var Γ}
  → {Δ : Con} → {w : Var Δ}
  → v ≡* w
  → var v ≡* var w
map-heq-var refl = refl

map-heq-lam
  : {Γ : Con} → {A : Ty Γ} → {F : Ty (Γ , A)} → {f : Tm (Γ , A)}
  → {Δ : Con} → {B : Ty Δ} → {G : Ty (Δ , B)} → {g : Tm (Δ , B)}
  → A ≡* B
  → F ≡* G
  → f ≡* g
  → lam A F f ≡* lam B G g
map-heq-lam refl refl refl = refl

map-heq-app
  : {Γ : Con} → {A : Ty Γ} → {F : Ty (Γ , A)} → {f x : Tm Γ}
  → {Δ : Con} → {B : Ty Δ} → {G : Ty (Δ , B)} → {g y : Tm Δ}
  → A ≡* B
  → F ≡* G
  → f ≡* g
  → x ≡* y
  → app A F f x ≡* app B G g y
map-heq-app refl refl refl refl = refl

map-heq-wkn-ty
  : {Γ : Con} → {A₁ : Ty Γ} → {T₁ : Ty Γ}
  → {Δ : Con} → {A₂ : Ty Δ} → {T₂ : Ty Δ}
  → A₁ ≡* A₂
  → T₁ ≡* T₂
  → A₁ [ wkn T₁ ] ≡* A₂ [ wkn T₂ ]
map-heq-wkn-ty refl refl = refl

map-heq-wkn-tm
  : {Γ : Con} → {t₁ : Tm Γ} → {T₁ : Ty Γ}
  → {Δ : Con} → {t₂ : Tm Δ} → {T₂ : Ty Δ}
  → t₁ ≡* t₂
  → T₁ ≡* T₂
  → t₁ [ wkn T₁ ] ≡* t₂ [ wkn T₂ ]
map-heq-wkn-tm refl refl = refl
