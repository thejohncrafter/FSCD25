module DefEq where

open import Agda.Builtin.Unit

open import Syntax
open import Wkn
open import Sub
open import IdxEq
open import MapHeq

open import Lemmas

data con-defeq : Con → Con → Set
data ty-defeq : {Γ Δ : Con} → Ty Γ → Ty Δ → Set
data var-defeq : {Γ Δ : Con} → Var Γ → Var Δ → Set
data tm-defeq : {Γ Δ : Con} → Tm Γ → Tm Δ → Set

data wkn-defeq
  : {Γ₁ Δ₁ : Con} → (σ₁ : Wkn Γ₁ Δ₁)
  → {Γ₂ Δ₂ : Con} → (σ₂ : Wkn Γ₂ Δ₂)
  → Set

data sub-defeq
  : {Γ₁ Δ₁ : Con} → (σ₁ : Sub Γ₁ Δ₁)
  → {Γ₂ Δ₂ : Con} → (σ₂ : Sub Γ₂ Δ₂)
  → Set

record DefEq (A : Set) (F : A → Set) : Set₁ where
  constructor mk-def-eq
  field
    _≡≡_ : {a b : A} → F a → F b → Set
  infix 4 _≡≡_

open DefEq {{ ... }} public

private
  data Domain : Set where
    mk : Con → Con → Domain

  wkn-eq-extent : Domain → Set
  wkn-eq-extent = λ { (mk Γ Δ) -> Wkn Γ Δ }

  sub-eq-extent : Domain → Set
  sub-eq-extent = λ { (mk Γ Δ) -> Sub Γ Δ }

instance
  denote-con-defeq : DefEq ⊤ (λ _ -> Con)
  denote-ty-defeq : DefEq Con Ty
  denote-var-defeq : DefEq Con Var
  denote-tm-defeq : DefEq Con Tm

  denote-wkn-defeq : DefEq Domain wkn-eq-extent
  denote-sub-defeq : DefEq Domain sub-eq-extent

  denote-con-defeq = mk-def-eq con-defeq
  denote-ty-defeq = mk-def-eq ty-defeq
  denote-var-defeq = mk-def-eq var-defeq
  denote-tm-defeq = mk-def-eq tm-defeq

  denote-wkn-defeq = mk-def-eq (λ { {mk _ _} {mk _ _} σ₁ σ₂ → wkn-defeq σ₁ σ₂ })
  denote-sub-defeq = mk-def-eq (λ { {mk _ _} {mk _ _} σ₁ σ₂ → sub-defeq σ₁ σ₂ })

data con-defeq where
  ⊥ : ⊥ ≡≡ ⊥
  cons
    : {Γ : Con} → {A : Ty Γ}
    → {Δ : Con} → {B : Ty Δ}
    → Γ ≡≡ Δ → A ≡≡ B
    → (Γ , A) ≡≡ (Δ , B)

data ty-defeq where
  U : {Γ Δ : Con} → Γ ≡≡ Δ → U {Γ} ≡≡ U {Δ}
  Pi
    : {Γ : Con} → {A : Ty Γ} → {F : Ty (Γ , A)}
    → {Δ : Con} → {B : Ty Δ} → {G : Ty (Δ , B)}
    → Γ ≡≡ Δ → A ≡≡ B → F ≡≡ G
    → Pi A F ≡≡ Pi B G
  El
    : {Γ : Con} → {t : Tm Γ}
    → {Δ : Con} → {u : Tm Δ}
    → Γ ≡≡ Δ → t ≡≡ u
    → El t ≡≡ El u

data var-defeq where
  here
    : {Γ : Con} → {A : Ty Γ}
    → {Δ : Con} → {B : Ty Δ}
    → Γ ≡≡ Δ → A ≡≡ B
    → here A ≡≡ here B
  there
    : {Γ : Con} → {A : Ty Γ} → {v : Var Γ}
    → {Δ : Con} → {B : Ty Δ} → {w : Var Δ}
    → Γ ≡≡ Δ → A ≡≡ B → v ≡≡ w
    → there {Γ} {A} v ≡≡ there {Δ} {B} w

data tm-defeq where
  var
    : {Γ : Con} → {v : Var Γ}
    → {Δ : Con} → {w : Var Δ}
    → Γ ≡≡ Δ → v ≡≡ w
    → var v ≡≡ var w
  lam
    : {Γ : Con} → {A : Ty Γ} → {F : Ty (Γ , A)} → {f : Tm (Γ , A)}
    → {Δ : Con} → {B : Ty Δ} → {G : Ty (Δ , B)} → {g : Tm (Δ , B)}
    → Γ ≡≡ Δ → A ≡≡ B → F ≡≡ G → f ≡≡ g
    → lam A F f ≡≡ lam B G g
  app
    : {Γ : Con} → {A : Ty Γ} → {F : Ty (Γ , A)} → {f : Tm Γ} → {x : Tm Γ}
    → {Δ : Con} → {B : Ty Δ} → {G : Ty (Δ , B)} → {g : Tm Δ} → {y : Tm Δ}
    → Γ ≡≡ Δ → A ≡≡ B → F ≡≡ G → f ≡≡ g → x ≡≡ y
    → app A F f x ≡≡ app B G g y
  beta
    : {Γ : Con} → {A : Ty Γ} → {F : Ty (Γ , A)} → {f : Tm (Γ , A)} → {x : Tm Γ}
    → {Δ : Con} → {B : Ty Δ} → {G : Ty (Δ , B)} → {g : Tm (Δ , B)} → {y : Tm Δ}
    → Γ ≡≡ Δ → A ≡≡ B → F ≡≡ G → f ≡≡ g → x ≡≡ y
    → app A F (lam A F f) x ≡≡ (g [ sub y ])
  eta
    : {Γ : Con} → {A : Ty Γ} → {F : Ty (Γ , A)} → {f : Tm (Γ , A)}
    → {Δ : Con} → {B : Ty Δ} → {G : Ty (Δ , B)} → {g : Tm (Δ , B)}
    → Γ ≡≡ Δ → A ≡≡ B → F ≡≡ G → f ≡≡ g
    → lam A F (app (A [ wkn A ]) (F [ wkn A ↑ A ]) f (var (here _))) ≡≡ lam B G g

data wkn-defeq where
  wkn
    : {Γ : Con} → {A : Ty Γ}
    → {Δ : Con} → {B : Ty Δ}
    → Γ ≡≡ Δ → A ≡≡ B
    → wkn A ≡≡ wkn B
  up
    : {Γ₁ Δ₁ : Con} → {σ₁ : Wkn Γ₁ Δ₁} → {A₁ : Ty Δ₁}
    → {Γ₂ Δ₂ : Con} → {σ₂ : Wkn Γ₂ Δ₂} → {A₂ : Ty Δ₂}
    → σ₁ ≡≡ σ₂ → A₁ ≡≡ A₂
    → σ₁ ↑ A₁ ≡≡ σ₂ ↑ A₂

data sub-defeq where
  sub
    : {Γ : Con} → {A : Ty Γ} → {t : Tm Γ}
    → {Δ : Con} → {B : Ty Δ} → {u : Tm Δ}
    → Γ ≡≡ Δ → A ≡≡ B → t ≡≡ u
    → sub {Γ} {A} t ≡≡ sub {Δ} {B} u
  up
    : {Γ₁ Δ₁ : Con} → {σ₁ : Sub Γ₁ Δ₁} → {A₁ : Ty Δ₁}
    → {Γ₂ Δ₂ : Con} → {σ₂ : Sub Γ₂ Δ₂} → {A₂ : Ty Δ₂}
    → σ₁ ≡≡ σ₂ → A₁ ≡≡ A₂
    → σ₁ ↑ A₁ ≡≡ σ₂ ↑ A₂

defeq-refl-con : (Γ : Con) → Γ ≡≡ Γ
defeq-refl-ty : {Γ : Con} → (A : Ty Γ) → A ≡≡ A
defeq-refl-var : {Γ : Con} → (v : Var Γ) → v ≡≡ v
defeq-refl-tm : {Γ : Con} → (t : Tm Γ) → t ≡≡ t

defeq-refl-con ⊥ = ⊥
defeq-refl-con (Γ , A) = cons (defeq-refl-con Γ) (defeq-refl-ty A)

defeq-refl-ty U = U (defeq-refl-con _)
defeq-refl-ty (Pi A B) = Pi (defeq-refl-con _) (defeq-refl-ty A) (defeq-refl-ty B)
defeq-refl-ty (El t) = El (defeq-refl-con _) (defeq-refl-tm t)

defeq-refl-var (here A) = here (defeq-refl-con _) (defeq-refl-ty A)
defeq-refl-var (there v) = there (defeq-refl-con _) (defeq-refl-ty _) (defeq-refl-var v)

defeq-refl-tm (var v) = var (defeq-refl-con _) (defeq-refl-var v)
defeq-refl-tm (lam A F f) = lam (defeq-refl-con _) (defeq-refl-ty A) (defeq-refl-ty F) (defeq-refl-tm f)
defeq-refl-tm (app A F f x) = app (defeq-refl-con _) (defeq-refl-ty A) (defeq-refl-ty F) (defeq-refl-tm f) (defeq-refl-tm x)

record LawfulDefEq (A : Set) (F : A → Set) {{ _ : IdxEq A F }} {{ _ : DefEq A F }} : Set₁ where
  constructor lawful
  field
    ≡≡-refl : {a : A} → {x : F a} → x ≡≡ x
    rw-l : {a b c : A} → {x : F a} → {y : F b} → {z : F c} → x ≡* y → y ≡≡ z → x ≡≡ z
    rw-r : {a b c : A} → {x : F a} → {y : F b} → {z : F c} → x ≡≡ y → y ≡* z → x ≡≡ z

  ≡≡-of-≡ : {a : A} → {x y : F a} → x ≡ y → x ≡≡ y
  ≡≡-of-≡ refl = ≡≡-refl

open LawfulDefEq {{ ... }} public

module ≡≡-reasoning
  {A : Set} {F : A → Set}
  {{ _ : IdxEq A F }} {{ _ : LawfulIdxEq A F }}
  {{ _ : DefEq A F }} {{ _ : LawfulDefEq A F }}
  where
  
  infix  1 begin≡≡_
  infixr 2 step-≡≡-⟨ step-≡≡-| step-≡≡-⟩
  infix  3 _≡≡∎

  begin≡≡_
    : ∀ {Γ Δ : A} {x : F Γ} {y : F Δ}
    → x ≡≡ y → x ≡≡ y
  begin≡≡_ x≡≡y = x≡≡y

  step-≡≡-| : ∀ {Γ Δ Σ : A} (x : F Γ) {y : F Δ} {z : F Σ} → y ≡* z → x ≡≡ y → x ≡≡ z
  step-≡≡-| x y≡*z  x≡≡y = rw-r x≡≡y y≡*z

  step-≡≡-⟨ : ∀ {Γ Δ Σ : A} (x : F Γ) {y : F Δ} {z : F Σ} → y ≡≡ z → x ≡* y → x ≡≡ z
  step-≡≡-⟨ x y≡≡z x≡*y = rw-l x≡*y y≡≡z

  step-≡≡-⟩ : ∀ {Γ Δ Σ : A} (x : F Γ) {y : F Δ} {z : F Σ} → y ≡* z → x ≡* y → x ≡* z
  step-≡≡-⟩ x y≡*z x≡*y = transitive x≡*y y≡*z

  syntax step-≡≡-| x y≡*z x≡≡y  =  x ≡≡⟨  x≡≡y ⟩ y≡*z
  syntax step-≡≡-⟨ x y≡≡z x≡*y =  x ≡≡*⟨  x≡*y ⟩ y≡≡z
  syntax step-≡≡-⟩ x y≡*z x≡*y =  x *≡≡⟨  x≡*y ⟩ y≡*z

  _≡≡∎ : ∀ {Γ : A} (x : F Γ) → x ≡* x
  x ≡≡∎ = reflexive

open ≡≡-reasoning {{ ... }} public

instance
  lawful-defeq-con : LawfulDefEq ⊤ (λ _ -> Con)
  lawful-defeq-ty : LawfulDefEq Con Ty
  lawful-defeq-var : LawfulDefEq Con Var
  lawful-defeq-tm : LawfulDefEq Con Tm

  lawful-defeq-con = lawful (defeq-refl-con _) (λ { refl h -> h }) (λ { h refl -> h })
  lawful-defeq-ty = lawful (defeq-refl-ty _) (λ { refl h -> h }) (λ { h refl -> h })
  lawful-defeq-var = lawful (defeq-refl-var _) (λ { refl h -> h }) (λ { h refl -> h })
  lawful-defeq-tm = lawful (defeq-refl-tm _) (λ { refl h -> h }) (λ { h refl -> h })

defeq-refl-wkn : {Γ Δ : Con} → (σ : Wkn Γ Δ) → σ ≡≡ σ
defeq-refl-wkn (wkn A) = wkn ≡≡-refl ≡≡-refl
defeq-refl-wkn (σ ↑ A) = up (defeq-refl-wkn σ) ≡≡-refl

defeq-refl-sub : {Γ Δ : Con} → (σ : Sub Γ Δ) → σ ≡≡ σ
defeq-refl-sub (sub x) = sub ≡≡-refl ≡≡-refl ≡≡-refl
defeq-refl-sub (σ ↑ A) = up (defeq-refl-sub σ) ≡≡-refl

defeq-map-wkn-con
  : {Γ₁ Δ₁ : Con} → {σ₁ : Wkn Γ₁ Δ₁}
  → {Γ₂ Δ₂ : Con} → {σ₂ : Wkn Γ₂ Δ₂}
  → σ₁ ≡≡ σ₂
  → Γ₁ ≡≡ Γ₂

defeq-map-wkn-ty
  : {Γ₁ Δ₁ : Con} → {σ₁ : Wkn Γ₁ Δ₁} → {A : Ty Δ₁}
  → {Γ₂ Δ₂ : Con} → {σ₂ : Wkn Γ₂ Δ₂} → {B : Ty Δ₂}
  → σ₁ ≡≡ σ₂ → A ≡≡ B
  → (A [ σ₁ ]) ≡≡ (B [ σ₂ ])

defeq-map-wkn-var
  : {Γ₁ Δ₁ : Con} → {σ₁ : Wkn Γ₁ Δ₁} → {v : Var Δ₁}
  → {Γ₂ Δ₂ : Con} → {σ₂ : Wkn Γ₂ Δ₂} → {w : Var Δ₂}
  → σ₁ ≡≡ σ₂ → v ≡≡ w
  → (v [ σ₁ ]) ≡≡ (w [ σ₂ ])

defeq-map-wkn-tm
  : {Γ₁ Δ₁ : Con} → {σ₁ : Wkn Γ₁ Δ₁} → {t : Tm Δ₁}
  → {Γ₂ Δ₂ : Con} → {σ₂ : Wkn Γ₂ Δ₂} → {u : Tm Δ₂}
  → σ₁ ≡≡ σ₂ → t ≡≡ u
  → (t [ σ₁ ]) ≡≡ (u [ σ₂ ])

defeq-map-wkn-con (wkn Γ≡≡Δ A≡≡B) = cons Γ≡≡Δ A≡≡B
defeq-map-wkn-con (up ≡σ≡ ≡A≡) = cons (defeq-map-wkn-con ≡σ≡) (defeq-map-wkn-ty ≡σ≡ ≡A≡)

defeq-map-wkn-ty ≡σ≡ (U ≡Δ≡) = U (defeq-map-wkn-con ≡σ≡)
defeq-map-wkn-ty ≡σ≡ (Pi ≡Δ≡ ≡A≡ ≡F≡) = Pi (defeq-map-wkn-con ≡σ≡) (defeq-map-wkn-ty ≡σ≡ ≡A≡) (defeq-map-wkn-ty (up ≡σ≡ ≡A≡) ≡F≡)
defeq-map-wkn-ty ≡σ≡ (El ≡Δ≡ ≡t≡) = El (defeq-map-wkn-con ≡σ≡) (defeq-map-wkn-tm ≡σ≡ ≡t≡)

defeq-map-wkn-var (wkn (cons ≡Γ≡ _) ≡T≡) (here ≡Δ≡ ≡A≡) = there (cons ≡Γ≡ ≡A≡) ≡T≡ (here ≡Γ≡ ≡A≡)
defeq-map-wkn-var (up ≡σ≡ ≡T≡)  (here ≡Δ≡ ≡A≡) = here (defeq-map-wkn-con ≡σ≡) (defeq-map-wkn-ty ≡σ≡ ≡A≡)
defeq-map-wkn-var (wkn (cons ≡Γ≡ _) ≡T≡) (there ≡Δ≡ ≡A≡ ≡v≡) = there (cons ≡Δ≡ ≡A≡) ≡T≡ (there ≡Δ≡ ≡A≡ ≡v≡)
defeq-map-wkn-var (up ≡σ≡ ≡T≡)  (there ≡Δ≡ ≡A≡ ≡v≡) = there (defeq-map-wkn-con ≡σ≡) (defeq-map-wkn-ty ≡σ≡ ≡A≡) (defeq-map-wkn-var ≡σ≡ ≡v≡)

defeq-map-wkn-tm ≡σ≡ (var ≡Δ≡ ≡v≡) = var (defeq-map-wkn-con ≡σ≡) (defeq-map-wkn-var ≡σ≡ ≡v≡)
defeq-map-wkn-tm ≡σ≡ (lam ≡Δ≡ ≡A≡ ≡F≡ ≡f≡) = lam (defeq-map-wkn-con ≡σ≡) (defeq-map-wkn-ty ≡σ≡ ≡A≡) (defeq-map-wkn-ty (up ≡σ≡ ≡A≡) ≡F≡) (defeq-map-wkn-tm (up ≡σ≡ ≡A≡) ≡f≡)
defeq-map-wkn-tm ≡σ≡ (app ≡Δ≡ ≡A≡ ≡F≡ ≡f≡ ≡x≡) = app (defeq-map-wkn-con ≡σ≡) (defeq-map-wkn-ty ≡σ≡ ≡A≡) (defeq-map-wkn-ty (up ≡σ≡ ≡A≡) ≡F≡) (defeq-map-wkn-tm ≡σ≡ ≡f≡) (defeq-map-wkn-tm ≡σ≡ ≡x≡)
defeq-map-wkn-tm {_} {_} {σ₁} {_} {_} {_} {σ₂} {_} ≡σ≡ (beta {Γ} {A} {F} {f} {x} {Δ} {B} {G} {g} {y} ≡Δ≡ ≡A≡ ≡F≡ ≡f≡ ≡x≡) =
  begin≡≡
      (app (A [ σ₁ ]) (F [ σ₁ ↑ A ]) (lam (A [ σ₁ ]) (F [ σ₁ ↑ A ]) (f [ σ₁ ↑ A ])) (x [ σ₁ ]))
    ≡≡⟨ beta (defeq-map-wkn-con ≡σ≡) (defeq-map-wkn-ty ≡σ≡ ≡A≡) (defeq-map-wkn-ty (up ≡σ≡ ≡A≡) ≡F≡) (defeq-map-wkn-tm (up ≡σ≡ ≡A≡) ≡f≡) (defeq-map-wkn-tm ≡σ≡ ≡x≡) ⟩
      (g [ σ₂ ↑ B ] [ sub (y [ σ₂ ]) ])
    *≡≡⟨ ≡*-of-eq (eq-symm (sub-wkn-tm B g σ₂ y)) ⟩
      (g [ sub y ] [ σ₂ ])
  ≡≡∎
defeq-map-wkn-tm {_} {_} {σ₁} {_} {_} {_} {σ₂} {_} ≡σ≡ (eta {Γ} {A} {F} {f} {Δ} {B} {G} {g} ≡Δ≡ ≡A≡ ≡F≡ ≡f≡) =
   begin≡≡
      (lam (A [ σ₁ ]) (F [ σ₁ ↑ A ]) (app (A [ wkn A ] [ σ₁ ↑ A ])      (F [ wkn A ↑ A ] [ σ₁ ↑ A ↑ (A [ wkn A ]) ])   (f [ σ₁ ↑ A ]) (var (here (A [ σ₁ ])))))
    ≡≡*⟨ map-heq-lam refl refl (map-heq-app (≡*-of-eq (up-wkn-ty _ _ _)) (up-wkn-ty-1 _ _ _ _) refl refl) ⟩
      (lam (A [ σ₁ ]) (F [ σ₁ ↑ A ]) (app (A [ σ₁ ] [ wkn (A [ σ₁ ]) ]) (F [ σ₁ ↑ A ] [ wkn (A [ σ₁ ]) ↑ (A [ σ₁ ]) ]) (f [ σ₁ ↑ A ]) (var (here (A [ σ₁ ])))))
    ≡≡⟨ eta (defeq-map-wkn-con ≡σ≡) (defeq-map-wkn-ty ≡σ≡ ≡A≡) (defeq-map-wkn-ty (up ≡σ≡ ≡A≡) ≡F≡) (defeq-map-wkn-tm (up ≡σ≡ ≡A≡) ≡f≡) ⟩
      lam (B [ σ₂ ]) (G [ σ₂ ↑ B ]) (g [ σ₂ ↑ B ])
  ≡≡∎

defeq-map-sub-con
  : {Γ₁ Δ₁ : Con} → {σ₁ : Sub Γ₁ Δ₁}
  → {Γ₂ Δ₂ : Con} → {σ₂ : Sub Γ₂ Δ₂}
  → σ₁ ≡≡ σ₂
  → Γ₁ ≡≡ Γ₂

defeq-map-sub-ty
  : {Γ₁ Δ₁ : Con} → {σ₁ : Sub Γ₁ Δ₁} → {A : Ty Δ₁}
  → {Γ₂ Δ₂ : Con} → {σ₂ : Sub Γ₂ Δ₂} → {B : Ty Δ₂}
  → σ₁ ≡≡ σ₂ → A ≡≡ B
  → (A [ σ₁ ]) ≡≡ (B [ σ₂ ])

defeq-map-sub-var
  : {Γ₁ Δ₁ : Con} → {σ₁ : Sub Γ₁ Δ₁} → {v : Var Δ₁}
  → {Γ₂ Δ₂ : Con} → {σ₂ : Sub Γ₂ Δ₂} → {w : Var Δ₂}
  → σ₁ ≡≡ σ₂ → v ≡≡ w
  → (v [ σ₁ ]) ≡≡ (w [ σ₂ ])

defeq-map-sub-tm
  : {Γ₁ Δ₁ : Con} → {σ₁ : Sub Γ₁ Δ₁} → {t : Tm Δ₁}
  → {Γ₂ Δ₂ : Con} → {σ₂ : Sub Γ₂ Δ₂} → {u : Tm Δ₂}
  → σ₁ ≡≡ σ₂ → t ≡≡ u
  → (t [ σ₁ ]) ≡≡ (u [ σ₂ ])

private
  rw-lemma-1
    : {Γ₁ Δ₁ : Con} → {σ₁ : Sub Γ₁ Δ₁} → {A : Ty Δ₁} → {v : Var Δ₁}
    → {Γ₂ Δ₂ : Con} → {σ₂ : Sub Γ₂ Δ₂} → {B : Ty Δ₂} → {w : Var Δ₂}
    → σ₁ ≡≡ σ₂ → A ≡≡ B → v ≡≡ w
    → v [ σ₁ ] [ wkn (A [ σ₁ ]) ] ≡ (v [ wkn A ] [ σ₁ ↑ A ])
  rw-lemma-1 {_} {_} {_} {_} {v} {_} {_} {_} {_} {w} _ _ _ = up-sub-var v _ _
  
  rw-lemma-2
    : {Γ₁ Δ₁ : Con} → {σ₁ : Sub Γ₁ Δ₁} → {A : Ty Δ₁} → {v : Var Δ₁}
    → {Γ₂ Δ₂ : Con} → {σ₂ : Sub Γ₂ Δ₂} → {B : Ty Δ₂} → {w : Var Δ₂}
    → σ₁ ≡≡ σ₂ → A ≡≡ B → v ≡≡ w
    → w [ σ₂ ] [ wkn (B [ σ₂ ]) ] ≡ (w [ wkn B ] [ σ₂ ↑ B ])
  rw-lemma-2 {_} {_} {_} {_} {v} {_} {_} {_} {_} {w} _ _ _ = up-sub-var w _ _

defeq-map-sub-con (sub Γ≡≡Δ A≡≡B x≡≡y) = Γ≡≡Δ
defeq-map-sub-con (up ≡σ≡ ≡A≡) = cons (defeq-map-sub-con ≡σ≡) (defeq-map-sub-ty ≡σ≡ ≡A≡)

defeq-map-sub-ty ≡σ≡ (U ≡Δ≡) = U (defeq-map-sub-con ≡σ≡)
defeq-map-sub-ty ≡σ≡ (Pi ≡Δ≡ ≡A≡ ≡F≡) = Pi (defeq-map-sub-con ≡σ≡) (defeq-map-sub-ty ≡σ≡ ≡A≡) (defeq-map-sub-ty (up ≡σ≡ ≡A≡) ≡F≡)
defeq-map-sub-ty ≡σ≡ (El ≡Δ≡ ≡t≡) = El (defeq-map-sub-con ≡σ≡) (defeq-map-sub-tm ≡σ≡ ≡t≡)

defeq-map-sub-var (sub ≡Γ≡ ≡T≡ ≡x≡) (here ≡Δ≡ ≡A≡) = ≡x≡
defeq-map-sub-var (up ≡σ≡ ≡T≡)      (here ≡Δ≡ ≡A≡) = var (cons (defeq-map-sub-con ≡σ≡) (defeq-map-sub-ty ≡σ≡ ≡A≡)) (here (defeq-map-sub-con ≡σ≡) (defeq-map-sub-ty ≡σ≡ ≡A≡))
defeq-map-sub-var (sub ≡Γ≡ ≡T≡ ≡x≡) (there ≡Δ≡ ≡A≡ ≡v≡) = var ≡Δ≡ ≡v≡
defeq-map-sub-var (up ≡σ≡ ≡T≡)      (there ≡Δ≡ ≡A≡ ≡v≡) rewrite rw-lemma-1 ≡σ≡ ≡A≡ ≡v≡ rewrite rw-lemma-2 ≡σ≡ ≡A≡ ≡v≡ =
  defeq-map-wkn-tm (wkn (defeq-map-sub-con ≡σ≡) (defeq-map-sub-ty ≡σ≡ ≡A≡)) (defeq-map-sub-var ≡σ≡ ≡v≡)

defeq-map-sub-tm ≡σ≡ (var ≡Δ≡ ≡v≡) = defeq-map-sub-var ≡σ≡ ≡v≡
defeq-map-sub-tm ≡σ≡ (lam ≡Δ≡ ≡A≡ ≡F≡ ≡f≡) = lam (defeq-map-sub-con ≡σ≡) (defeq-map-sub-ty ≡σ≡ ≡A≡) (defeq-map-sub-ty (up ≡σ≡ ≡A≡) ≡F≡) (defeq-map-sub-tm (up ≡σ≡ ≡A≡) ≡f≡)
defeq-map-sub-tm ≡σ≡ (app ≡Δ≡ ≡A≡ ≡F≡ ≡f≡ ≡x≡) = app (defeq-map-sub-con ≡σ≡) (defeq-map-sub-ty ≡σ≡ ≡A≡) (defeq-map-sub-ty (up ≡σ≡ ≡A≡) ≡F≡) (defeq-map-sub-tm ≡σ≡ ≡f≡) (defeq-map-sub-tm ≡σ≡ ≡x≡)
defeq-map-sub-tm {_} {_} {σ₁} {_} {_} {_} {σ₂} {_} ≡σ≡ (beta {Γ} {A} {F} {f} {x} {Δ} {B} {G} {g} {y} ≡Δ≡ ≡A≡ ≡F≡ ≡f≡ ≡x≡) =
  begin≡≡
      (app (A [ σ₁ ]) (F [ σ₁ ↑ A ]) (lam (A [ σ₁ ]) (F [ σ₁ ↑ A ]) (f [ σ₁ ↑ A ])) (x [ σ₁ ]))
    ≡≡⟨ beta (defeq-map-sub-con ≡σ≡) (defeq-map-sub-ty ≡σ≡ ≡A≡) (defeq-map-sub-ty (up ≡σ≡ ≡A≡) ≡F≡) (defeq-map-sub-tm (up ≡σ≡ ≡A≡) ≡f≡) (defeq-map-sub-tm ≡σ≡ ≡x≡) ⟩
      (g [ σ₂ ↑ B ] [ sub (y [ σ₂ ]) ])
    *≡≡⟨ ≡*-of-eq (eq-symm (sub-sub-tm B g σ₂ y)) ⟩
      (g [ sub y ] [ σ₂ ])
  ≡≡∎
defeq-map-sub-tm {_} {_} {σ₁} {_} {_} {_} {σ₂} {_} ≡σ≡ (eta {Γ} {A} {F} {f} {Δ} {B} {G} {g} ≡Δ≡ ≡A≡ ≡F≡ ≡f≡) =
   begin≡≡
      (lam (A [ σ₁ ]) (F [ σ₁ ↑ A ]) (app (A [ wkn A ] [ σ₁ ↑ A ])      (F [ wkn A ↑ A ] [ σ₁ ↑ A ↑ (A [ wkn A ]) ])   (f [ σ₁ ↑ A ]) (var (here (A [ σ₁ ])))))
    ≡≡*⟨ map-heq-lam refl refl (map-heq-app (≡*-of-eq (up-sub-ty _ _ _)) (up-sub-ty-1 _ _ _ _) refl refl) ⟩
      (lam (A [ σ₁ ]) (F [ σ₁ ↑ A ]) (app (A [ σ₁ ] [ wkn (A [ σ₁ ]) ]) (F [ σ₁ ↑ A ] [ wkn (A [ σ₁ ]) ↑ (A [ σ₁ ]) ]) (f [ σ₁ ↑ A ]) (var (here (A [ σ₁ ])))))
    ≡≡⟨ eta (defeq-map-sub-con ≡σ≡) (defeq-map-sub-ty ≡σ≡ ≡A≡) (defeq-map-sub-ty (up ≡σ≡ ≡A≡) ≡F≡) (defeq-map-sub-tm (up ≡σ≡ ≡A≡) ≡f≡) ⟩
      lam (B [ σ₂ ]) (G [ σ₂ ↑ B ]) (g [ σ₂ ↑ B ])
  ≡≡∎
