module IdxEq where

open import Agda.Builtin.Unit
open import Agda.Builtin.Equality public

open import Syntax
open import Wkn
open import Sub

≡-symm : {A : Set} → {a b : A} → a ≡ b → b ≡ a
≡-symm refl = refl

data ty-eq : {Γ Δ : Con} → (x : Ty Γ) → (y : Ty Δ) → Set where
  refl : {Γ : Con} → {x : Ty Γ} → ty-eq x x

data var-eq : {Γ Δ : Con} → (x : Var Γ) → (y : Var Δ) → Set where
  refl : {Γ : Con} → {x : Var Γ} → var-eq x x

data tm-eq : {Γ Δ : Con} → (x : Tm Γ) → (y : Tm Δ) → Set where
  refl : {Γ : Con} → {x : Tm Γ} → tm-eq x x

data wkn-eq
  : {Γ₁ Δ₁ : Con} → (σ₁ : Wkn Γ₁ Δ₁)
  → {Γ₂ Δ₂ : Con} → (σ₂ : Wkn Γ₂ Δ₂)
  → Set

data sub-eq
  : {Γ₁ Δ₁ : Con} → (σ₁ : Sub Γ₁ Δ₁)
  → {Γ₂ Δ₂ : Con} → (σ₂ : Sub Γ₂ Δ₂)
  → Set

record IdxEq (A : Set) (F : A → Set) : Set₁ where
  constructor mk-idxeq
  field
    _≡*_ : {a b : A} → F a → F b → Set
  infix 4 _≡*_

open IdxEq {{ ... }} public

record LawfulIdxEq (A : Set) (F : A → Set) {{ _ : IdxEq A F }} : Set₁ where
  constructor is-lawful
  field
    reflexive : {Γ : A} → {x : F Γ} → x ≡* x
    transitive
      : {Γ Δ Σ : A}
      → {x : F Γ} → {y : F Δ} → {z : F Σ}
      → x ≡* y → y ≡* z → x ≡* z
    symmetric
      : {Γ Δ : A}
      → {x : F Γ} → {y : F Δ}
      → x ≡* y → y ≡* x

open LawfulIdxEq {{ ... }} public

private
  data Domain : Set where
    mk : Con → Con → Domain

  wkn-eq-extent : Domain → Set
  wkn-eq-extent = λ { (mk Γ Δ) -> Wkn Γ Δ }

  sub-eq-extent : Domain → Set
  sub-eq-extent = λ { (mk Γ Δ) -> Sub Γ Δ }

instance
  denote-con-eq : IdxEq ⊤ (λ _ → Con)
  denote-ty-eq : IdxEq Con Ty
  denote-var-eq : IdxEq Con Var
  denote-tm-eq : IdxEq Con Tm

  denote-con-eq = mk-idxeq _≡_
  denote-ty-eq = mk-idxeq ty-eq
  denote-var-eq = mk-idxeq var-eq
  denote-tm-eq = mk-idxeq tm-eq

  denote-wkn-eq : IdxEq Domain wkn-eq-extent
  denote-sub-eq : IdxEq Domain sub-eq-extent

  denote-wkn-eq = mk-idxeq (λ { {mk _ _} {mk _ _} σ₁ σ₂ → wkn-eq σ₁ σ₂ })
  denote-sub-eq = mk-idxeq (λ { {mk _ _} {mk _ _} σ₁ σ₂ → sub-eq σ₁ σ₂ })

data wkn-eq where
  wkn
    : {Γ : Con} → {A : Ty Γ}
    → {Δ : Con} → {B : Ty Δ}
    → Γ ≡* Δ → A ≡* B
    → wkn A ≡* wkn B
  up
    : {Γ₁ Δ₁ : Con} → {σ₁ : Wkn Γ₁ Δ₁} → {A₁ : Ty Δ₁}
    → {Γ₂ Δ₂ : Con} → {σ₂ : Wkn Γ₂ Δ₂} → {A₂ : Ty Δ₂}
    → σ₁ ≡* σ₂ → A₁ ≡* A₂
    → σ₁ ↑ A₁ ≡* σ₂ ↑ A₂

data sub-eq where
  sub
    : {Γ : Con} → {A : Ty Γ} → {t : Tm Γ}
    → {Δ : Con} → {B : Ty Δ} → {u : Tm Δ}
    → Γ ≡* Δ → A ≡* B → t ≡* u
    → sub {Γ} {A} t ≡* sub {Δ} {B} u
  up
    : {Γ₁ Δ₁ : Con} → {σ₁ : Sub Γ₁ Δ₁} → {A₁ : Ty Δ₁}
    → {Γ₂ Δ₂ : Con} → {σ₂ : Sub Γ₂ Δ₂} → {A₂ : Ty Δ₂}
    → σ₁ ≡* σ₂ → A₁ ≡* A₂
    → σ₁ ↑ A₁ ≡* σ₂ ↑ A₂

eq-symm : {A : Set} → {x y : A} → x ≡ y → y ≡ x
eq-symm refl = refl

eq-of-ty-idxeq
  : {Γ : Con} → {A B : Ty Γ}
  → A ≡* B
  → A ≡ B
eq-of-ty-idxeq refl = refl

eq-of-var-idxeq
  : {Γ : Con} → {v w : Var Γ}
  → v ≡* w
  → v ≡ w
eq-of-var-idxeq refl = refl

eq-of-tm-idxeq
  : {Γ : Con} → {t u : Tm Γ}
  → t ≡* u
  → t ≡ u
eq-of-tm-idxeq refl = refl

module ≡*-reasoning
  {A : Set} {F : A → Set}
  {{ _ : IdxEq A F }}
  {{ _ : LawfulIdxEq A F }}
  where
  
  infix  1 begin_
  infixr 2 step-≡*-| step-≡*-⟩
  infix  3 _∎

  begin_
    : ∀ {Γ Δ : A} {x : F Γ} {y : F Δ}
    → x ≡* y → x ≡* y
  begin x≡*y = x≡*y

  step-≡*-| : ∀ {Γ Δ : A} (x : F Γ) {y : F Δ} → x ≡* y → x ≡* y
  step-≡*-| x x≡*y = x≡*y

  step-≡*-⟩ : ∀ {Γ Δ Σ : A} (x : F Γ) {y : F Δ} {z : F Σ} → y ≡* z → x ≡* y → x ≡* z
  step-≡*-⟩ x y≡*z x≡*y = transitive x≡*y y≡*z

  syntax step-≡*-| x x≡*y      =  x ≡*⟨⟩ x≡*y
  syntax step-≡*-⟩ x y≡*z x≡*y  =  x ≡*⟨  x≡*y ⟩ y≡*z

  _∎ : ∀ {Γ : A} (x : F Γ) → x ≡* x
  x ∎ = reflexive

  ≡*-of-eq : ∀ {Γ : A} {x y : F Γ} → x ≡ y → x ≡* y
  ≡*-of-eq refl = reflexive

open ≡*-reasoning {{ ... }} public

instance
  lawful-con-eq : LawfulIdxEq ⊤ (λ _ -> Con)
  lawful-ty-eq : LawfulIdxEq Con Ty
  lawful-var-eq : LawfulIdxEq Con Var
  lawful-tm-eq : LawfulIdxEq Con Tm

  lawful-con-eq = is-lawful refl (λ { refl refl -> refl }) (λ { refl -> refl })
  lawful-ty-eq = is-lawful refl (λ { refl refl -> refl }) (λ { refl -> refl })
  lawful-var-eq = is-lawful refl (λ { refl refl -> refl }) (λ { refl -> refl })
  lawful-tm-eq = is-lawful refl (λ { refl refl -> refl }) (λ { refl -> refl })
