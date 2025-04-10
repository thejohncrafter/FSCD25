module Typing where

open import Agda.Builtin.Unit

open import Syntax
open import Wkn
open import Sub
open import IdxEq
open import DefEq

open import Lemmas

data _⊢     : (Γ : Con) → Set
data _⊢_    : (Γ : Con) → Ty Γ → Set
data _⊢_∈v_ : (Γ : Con) → Var Γ → Ty Γ → Set
data _⊢_∈_  : (Γ : Con) → Tm Γ → Ty Γ → Set

data _⊢ where
  ⊥ : ⊥ ⊢
  cons
    : {Γ : Con} → {A : Ty Γ}
    → Γ ⊢ → Γ ⊢ A
    → (Γ , A) ⊢

data _⊢_ where
  U : {Γ : Con} → Γ ⊢ → Γ ⊢ U {Γ}
  Pi
    : {Γ : Con} → {A : Ty Γ} → {F : Ty (Γ , A)}
    → Γ ⊢ → Γ ⊢ A → (Γ , A) ⊢ F
    → Γ ⊢ Pi A F
  El
    : {Γ : Con} → {t : Tm Γ}
    → Γ ⊢ → Γ ⊢ t ∈ U
    → Γ ⊢ El t

data _⊢_∈v_ where
  here
    : {Γ : Con} → {A : Ty Γ}
    → Γ ⊢ → Γ ⊢ A
    → (Γ , A) ⊢ here A ∈v (A [ wkn A ])
  there
    : {Γ : Con} → {A T : Ty Γ} → {v : Var Γ}
    → Γ ⊢ → Γ ⊢ A → Γ ⊢ T → Γ ⊢ v ∈v A
    → (Γ , T) ⊢ there v ∈v (A [ wkn T ])

data _⊢_∈_ where
  var
    : {Γ : Con} → {A : Ty Γ} → {v : Var Γ}
    → Γ ⊢ → Γ ⊢ A → Γ ⊢ v ∈v A
    → Γ ⊢ var v ∈ A
  lam
    : {Γ : Con} → {A : Ty Γ} → {F : Ty (Γ , A)} → {f : Tm (Γ , A)}
    → Γ ⊢ → Γ ⊢ A → (Γ , A) ⊢ F → (Γ , A) ⊢ f ∈ F
    → Γ ⊢ lam A F f ∈ Pi A F
  app
    : {Γ : Con} → {A : Ty Γ} → {F : Ty (Γ , A)} → {f : Tm Γ} → {x : Tm Γ}
    → Γ ⊢ → Γ ⊢ A → (Γ , A) ⊢ F → Γ ⊢ f ∈ Pi A F → Γ ⊢ x ∈ A
    → Γ ⊢ app A F f x ∈ (F [ sub x ])
  cast
    : {Γ : Con} → {A B : Ty Γ} → {t : Tm Γ}
    → Γ ⊢ → Γ ⊢ A → Γ ⊢ B → Γ ⊢ t ∈ A
    → A ≡≡ B
    → Γ ⊢ t ∈ B

data wkn-typing : (Γ Δ : Con) → Wkn Γ Δ → Set
data sub-typing : (Γ Δ : Con) → Sub Γ Δ → Set

syntax wkn-typing Γ Δ σ = Γ ⊢ σ ∈w Δ
syntax sub-typing Γ Δ σ = Γ ⊢ σ ∈s Δ

data wkn-typing where
  wkn
    : {Γ : Con} → {A : Ty Γ}
    → Γ ⊢ → Γ ⊢ A
    → (Γ , A) ⊢ wkn A ∈w Γ
  up
    : {Γ Δ : Con} → {σ : Wkn Γ Δ} → {A : Ty Δ}
    → Δ ⊢ → Γ ⊢ σ ∈w Δ → Δ ⊢ A
    → (Γ , A [ σ ]) ⊢ σ ↑ A ∈w (Δ , A)

data sub-typing where
  sub
    : {Γ : Con} → {A : Ty Γ} → {x : Tm Γ}
    → Γ ⊢ → Γ ⊢ A → Γ ⊢ x ∈ A
    → Γ ⊢ sub x ∈s (Γ , A)
  up
    : {Γ Δ : Con} → {σ : Sub Γ Δ} → {A : Ty Δ}
    → Δ ⊢ → Γ ⊢ σ ∈s Δ → Δ ⊢ A
    → (Γ , A [ σ ]) ⊢ σ ↑ A ∈s (Δ , A)

private
  rw-lemma-1 : {Γ Δ : Con} → {σ : Wkn Γ Δ} → Γ ⊢ σ ∈w Δ → {A : Ty Δ} → {F : Ty (Δ , A)} → {x : Tm Δ} → Δ ⊢ A → (Δ , A) ⊢ F → Δ ⊢ x ∈ A → (F [ sub x ] [ σ ]) ≡ (F [ σ ↑ A ] [ sub (x [ σ ]) ])
  rw-lemma-1 _ _ _ _ = sub-wkn-ty _ _ _ _

  rw-lemma-2 : {Γ Δ : Con} → {σ : Wkn Γ Δ} → Γ ⊢ σ ∈w Δ → {A T : Ty Δ} → Δ ⊢ A → Δ ⊢ T → (A [ wkn T ] [ σ ↑ T ]) ≡ (A [ σ ] [ wkn (T [ σ ]) ])
  rw-lemma-2 _ _ _ = up-wkn-ty _ _ _

map-wkn-con : {Γ Δ : Con} → {σ : Wkn Γ Δ} → Γ ⊢ σ ∈w Δ → Δ ⊢ → Γ ⊢
map-wkn-ty  : {Γ Δ : Con} → {σ : Wkn Γ Δ} → Γ ⊢ σ ∈w Δ → {A : Ty Δ} → Δ ⊢ A → Γ ⊢ (A [ σ ])
map-wkn-var : {Γ Δ : Con} → {σ : Wkn Γ Δ} → Γ ⊢ σ ∈w Δ → {A : Ty Δ} → {v : Var Δ} → Δ ⊢ v ∈v A → Γ ⊢ (v [ σ ]) ∈v (A [ σ ])
map-wkn-tm  : {Γ Δ : Con} → {σ : Wkn Γ Δ} → Γ ⊢ σ ∈w Δ → {A : Ty Δ} → {t : Tm Δ}  → Δ ⊢ t ∈  A → Γ ⊢ (t [ σ ]) ∈  (A [ σ ])

map-wkn-con (wkn _ Γ⊢A) Γ⊢ = cons Γ⊢ Γ⊢A
map-wkn-con (up _ Γ⊢σ∈wΔ _) (cons Δ⊢ Δ⊢A) = cons (map-wkn-con Γ⊢σ∈wΔ Δ⊢) (map-wkn-ty Γ⊢σ∈wΔ Δ⊢A)

map-wkn-ty Γ⊢σ∈wΔ (U Δ⊢) = U (map-wkn-con Γ⊢σ∈wΔ Δ⊢)
map-wkn-ty Γ⊢σ∈wΔ (Pi Δ⊢ Δ⊢A Δ,A⊢F) = Pi (map-wkn-con Γ⊢σ∈wΔ Δ⊢) (map-wkn-ty Γ⊢σ∈wΔ Δ⊢A) (map-wkn-ty (up Δ⊢ Γ⊢σ∈wΔ Δ⊢A) Δ,A⊢F)
map-wkn-ty Γ⊢σ∈wΔ (El Δ⊢ Δ⊢t∈U) = El (map-wkn-con Γ⊢σ∈wΔ Δ⊢) (map-wkn-tm Γ⊢σ∈wΔ Δ⊢t∈U)

map-wkn-var (wkn _ Δ,A⊢T) (here Δ⊢ Δ⊢A) = there (cons Δ⊢ Δ⊢A) (map-wkn-ty (wkn Δ⊢ Δ⊢A) Δ⊢A) Δ,A⊢T (here Δ⊢ Δ⊢A)
map-wkn-var (up _ Γ⊢σ∈wΔ _) (here Δ⊢ Δ⊢A) rewrite rw-lemma-2 Γ⊢σ∈wΔ Δ⊢A Δ⊢A = here (map-wkn-con Γ⊢σ∈wΔ Δ⊢) (map-wkn-ty Γ⊢σ∈wΔ Δ⊢A)
map-wkn-var (wkn _ Δ,T⊢A) (there Δ⊢ Δ⊢A Δ⊢T Δ⊢v∈A) = there (cons Δ⊢ Δ⊢T) (map-wkn-ty (wkn Δ⊢ Δ⊢T) Δ⊢A) Δ,T⊢A (there Δ⊢ Δ⊢A Δ⊢T Δ⊢v∈A)
map-wkn-var (up _ Γ⊢σ∈wΔ _) (there Δ⊢ Δ⊢A Δ⊢T Δ⊢v∈A) rewrite rw-lemma-2 Γ⊢σ∈wΔ Δ⊢A Δ⊢T = there (map-wkn-con Γ⊢σ∈wΔ Δ⊢) (map-wkn-ty Γ⊢σ∈wΔ Δ⊢A) (map-wkn-ty Γ⊢σ∈wΔ Δ⊢T) (map-wkn-var Γ⊢σ∈wΔ Δ⊢v∈A)

map-wkn-tm Γ⊢σ∈wΔ (var Δ⊢ Δ⊢A Δ⊢v∈vA) = var (map-wkn-con Γ⊢σ∈wΔ Δ⊢) (map-wkn-ty Γ⊢σ∈wΔ Δ⊢A) (map-wkn-var Γ⊢σ∈wΔ Δ⊢v∈vA)
map-wkn-tm Γ⊢σ∈wΔ (lam Δ⊢ Δ⊢A Δ,A⊢F Δ,A⊢f∈F) = lam (map-wkn-con Γ⊢σ∈wΔ Δ⊢) (map-wkn-ty Γ⊢σ∈wΔ Δ⊢A) (map-wkn-ty (up Δ⊢ Γ⊢σ∈wΔ Δ⊢A) Δ,A⊢F) (map-wkn-tm (up Δ⊢ Γ⊢σ∈wΔ Δ⊢A) Δ,A⊢f∈F)
map-wkn-tm Γ⊢σ∈wΔ (app Δ⊢ Δ⊢A Δ,A⊢F Δ⊢f∈ Δ⊢x∈) rewrite rw-lemma-1 Γ⊢σ∈wΔ Δ⊢A Δ,A⊢F Δ⊢x∈ =
  app (map-wkn-con Γ⊢σ∈wΔ Δ⊢) (map-wkn-ty Γ⊢σ∈wΔ Δ⊢A) (map-wkn-ty (up Δ⊢ Γ⊢σ∈wΔ Δ⊢A) Δ,A⊢F) (map-wkn-tm Γ⊢σ∈wΔ Δ⊢f∈) (map-wkn-tm Γ⊢σ∈wΔ Δ⊢x∈)
map-wkn-tm Γ⊢σ∈wΔ (cast Δ⊢ Δ⊢A Δ⊢B Δ⊢t∈A A≡B) = cast (map-wkn-con Γ⊢σ∈wΔ Δ⊢) (map-wkn-ty Γ⊢σ∈wΔ Δ⊢A) (map-wkn-ty Γ⊢σ∈wΔ Δ⊢B) (map-wkn-tm Γ⊢σ∈wΔ Δ⊢t∈A) (defeq-map-wkn-ty (defeq-refl-wkn _) A≡B)

private
  rw-lemma-3 : {Γ Δ : Con} → {σ : Sub Γ Δ} → Γ ⊢ σ ∈s Δ → {A : Ty Δ} → {F : Ty (Δ , A)} → {x : Tm Δ} → Δ ⊢ A → (Δ , A) ⊢ F → Δ ⊢ x ∈ A → (F [ sub x ] [ σ ]) ≡ (F [ σ ↑ A ] [ sub (x [ σ ]) ])
  rw-lemma-3 _ _ _ _ = sub-sub-ty _ _ _ _

  rw-lemma-4 : {Γ Δ : Con} → {σ : Sub Γ Δ} → Γ ⊢ σ ∈s Δ → {A T : Ty Δ} → Δ ⊢ A → Δ ⊢ T → (A [ wkn T ] [ σ ↑ T ]) ≡ (A [ σ ] [ wkn (T [ σ ]) ])
  rw-lemma-4 _ _ _ = up-sub-ty _ _ _

  rw-lemma-5 : {Γ : Con} → {A : Ty Γ} → {x : Tm Γ} → Γ ⊢ x ∈ A → (A [ wkn A ] [ sub x ]) ≡ A
  rw-lemma-5 _ = wkn-sub-ty _ _ _

  rw-lemma-6 : {Γ : Con} → {A T : Ty Γ} → {x : Tm Γ} → Γ ⊢ A → Γ ⊢ x ∈ T → (A [ wkn T ] [ sub x ]) ≡ A
  rw-lemma-6 _ _ = wkn-sub-ty _ _ _

map-sub-con : {Γ Δ : Con} → {σ : Sub Γ Δ} → Γ ⊢ σ ∈s Δ → Δ ⊢ → Γ ⊢
map-sub-ty  : {Γ Δ : Con} → {σ : Sub Γ Δ} → Γ ⊢ σ ∈s Δ → {A : Ty Δ} → Δ ⊢ A → Γ ⊢ (A [ σ ])
map-sub-var : {Γ Δ : Con} → {σ : Sub Γ Δ} → Γ ⊢ σ ∈s Δ → {A : Ty Δ} → {v : Var Δ} → Δ ⊢ v ∈v A → Γ ⊢ (v [ σ ]) ∈ (A [ σ ])
map-sub-tm  : {Γ Δ : Con} → {σ : Sub Γ Δ} → Γ ⊢ σ ∈s Δ → {A : Ty Δ} → {t : Tm Δ}  → Δ ⊢ t ∈  A → Γ ⊢ (t [ σ ]) ∈ (A [ σ ])

map-sub-con (sub Γ⊢ Γ⊢A Γ⊢x∈A) _ = Γ⊢
map-sub-con (up _ Γ⊢σ∈sΔ _) (cons Δ⊢ Δ⊢A) = cons (map-sub-con Γ⊢σ∈sΔ Δ⊢) (map-sub-ty Γ⊢σ∈sΔ Δ⊢A)

map-sub-ty Γ⊢σ∈sΔ (U Δ⊢) = U (map-sub-con Γ⊢σ∈sΔ Δ⊢)
map-sub-ty Γ⊢σ∈sΔ (Pi Δ⊢ Δ⊢A Δ,A⊢F) = Pi (map-sub-con Γ⊢σ∈sΔ Δ⊢) (map-sub-ty Γ⊢σ∈sΔ Δ⊢A) (map-sub-ty (up Δ⊢ Γ⊢σ∈sΔ Δ⊢A) Δ,A⊢F)
map-sub-ty Γ⊢σ∈sΔ (El Δ⊢ Δ⊢t∈U) = El (map-sub-con Γ⊢σ∈sΔ Δ⊢) (map-sub-tm Γ⊢σ∈sΔ Δ⊢t∈U)

map-sub-var (sub _ Δ⊢T Δ⊢x∈T)   (here Δ⊢ Δ⊢A) rewrite rw-lemma-5 Δ⊢x∈T = Δ⊢x∈T
map-sub-var (up _ Γ⊢σ∈sΔ _)     (here Δ⊢ Δ⊢A) rewrite rw-lemma-4 Γ⊢σ∈sΔ Δ⊢A Δ⊢A = var (cons (map-sub-con Γ⊢σ∈sΔ Δ⊢) (map-sub-ty Γ⊢σ∈sΔ Δ⊢A)) (map-wkn-ty (wkn (map-sub-con Γ⊢σ∈sΔ Δ⊢) (map-sub-ty Γ⊢σ∈sΔ Δ⊢A)) (map-sub-ty Γ⊢σ∈sΔ Δ⊢A)) (here (map-sub-con Γ⊢σ∈sΔ Δ⊢) (map-sub-ty Γ⊢σ∈sΔ Δ⊢A))
map-sub-var (sub _ _ Δ⊢x∈T)     (there Δ⊢ Δ⊢A Δ⊢T Δ⊢v∈A) rewrite rw-lemma-6 Δ⊢A Δ⊢x∈T = var Δ⊢ Δ⊢A Δ⊢v∈A
map-sub-var (up _ Γ⊢σ∈sΔ Δ⊢x∈T) (there Δ⊢ Δ⊢A Δ⊢T Δ⊢v∈A) rewrite rw-lemma-4 Γ⊢σ∈sΔ Δ⊢A Δ⊢T = map-wkn-tm (wkn (map-sub-con Γ⊢σ∈sΔ Δ⊢) (map-sub-ty Γ⊢σ∈sΔ Δ⊢T)) (map-sub-var Γ⊢σ∈sΔ Δ⊢v∈A)

map-sub-tm Γ⊢σ∈wΔ (var Δ⊢ Δ⊢A Δ⊢v∈vA) = map-sub-var Γ⊢σ∈wΔ Δ⊢v∈vA
map-sub-tm Γ⊢σ∈wΔ (lam Δ⊢ Δ⊢A Δ,A⊢F Δ,A⊢f∈F) = lam (map-sub-con Γ⊢σ∈wΔ Δ⊢) (map-sub-ty Γ⊢σ∈wΔ Δ⊢A) (map-sub-ty (up Δ⊢ Γ⊢σ∈wΔ Δ⊢A) Δ,A⊢F) (map-sub-tm (up Δ⊢ Γ⊢σ∈wΔ Δ⊢A) Δ,A⊢f∈F)
map-sub-tm Γ⊢σ∈wΔ (app Δ⊢ Δ⊢A Δ,A⊢F Δ⊢f∈ Δ⊢x∈) rewrite rw-lemma-3 Γ⊢σ∈wΔ Δ⊢A Δ,A⊢F Δ⊢x∈ =
  app (map-sub-con Γ⊢σ∈wΔ Δ⊢) (map-sub-ty Γ⊢σ∈wΔ Δ⊢A) (map-sub-ty (up Δ⊢ Γ⊢σ∈wΔ Δ⊢A) Δ,A⊢F) (map-sub-tm Γ⊢σ∈wΔ Δ⊢f∈) (map-sub-tm Γ⊢σ∈wΔ Δ⊢x∈)
map-sub-tm Γ⊢σ∈wΔ (cast Δ⊢ Δ⊢A Δ⊢B Δ⊢t∈A A≡B) = cast (map-sub-con Γ⊢σ∈wΔ Δ⊢) (map-sub-ty Γ⊢σ∈wΔ Δ⊢A) (map-sub-ty Γ⊢σ∈wΔ Δ⊢B) (map-sub-tm Γ⊢σ∈wΔ Δ⊢t∈A) (defeq-map-sub-ty (defeq-refl-sub _) A≡B)
