module Sem where

open import Lambda
open import Value

open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; cong; cong₂)
open import Data.Nat using (ℕ; suc ; zero)
open import Data.Product using (_×_; Σ; Σ-syntax; ∃; ∃-syntax; proj₁; proj₂)
  renaming (_,_ to ⟨_,_⟩)
open import Data.Sum
open import Agda.Primitive using (lzero)
open import Lambda
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Negation using (contradiction)
open import Data.Empty using (⊥-elim) renaming (⊥ to Bot)
open import Relation.Nullary using (Dec; yes; no)
open import Data.Unit

Sem : Context → Set₁
Sem Γ = (Env Γ → Value → Set)

infix 3 _≃_

_≃_ : ∀ {Γ} → (Sem Γ) → (Sem Γ) → Set
_≃_ {Γ} D₁ D₂ = ∀{γ : Env Γ} {v} → D₁ γ v iff D₂ γ v

ℬ : ∀{B : Base} → base-rep B → Value
ℬ {Nat} n = lit n
ℬ {𝔹} b = lit b

data ℘ : ∀{P : Prim} → rep P → Value → Set where
   ℘-base : ∀{B}{b : base-rep B}
              ---------------
            → ℘ {` B} b (ℬ b)
   ℘-fun :  ∀{B}{P}{f : base-rep B → rep P}{k : base-rep B}{v : Value}
            → ℘ {P} (f k) v
              ---------------------------
            → ℘ {B ⇒ P} f (lit {B} k ↦ v)
   ℘-⊔ :  ∀{P : Prim}{p : rep P}{v₁ v₂ : Value}
            → ℘ {P} p v₁  →  ℘ {P} p v₂
              -------------------------
            → ℘ {P} p (v₁ ⊔ v₂)
   ℘-⊥ :  ∀{P : Prim}{p : rep P}
              ---------
            → ℘ {P} p ⊥


data ℰ : ∀{Γ} → Γ ⊢ ★ → Env Γ → Value → Set where
  ℰ-var : ∀ {Γ} {γ : Env Γ} {x v}
                   → v ⊑ nth x γ
        -----------
      → ℰ (` x) γ v
  ℰ-lit : ∀{Γ}{γ : Env Γ}{P : Prim} {p : rep P} {v : Value}
        → ℘ {P} p v
          --------------------
        → ℰ ($_ {Γ} {P} p) γ v
  ℰ-app : ∀ {Γ} {γ : Env Γ} {M₁ M₂ v v₁ v₂}
        → ℰ M₁ γ (v₁ ↦ v₂)  →  ℰ M₂ γ v₁   → v ⊑ v₂
          ----------------------------------
        → ℰ (M₁ · M₂) γ v


{-


Λ : ∀{Γ} → Sem (Γ , ★) → Sem Γ
Λ S' γ ⊥ = ⊤
Λ S' γ (lit x) = Bot
Λ S' γ (v₁ ↦ v₂) = S' (γ , v₁) v₂
Λ S' γ (v₁ ⊔ v₂) = (Λ S' γ v₁) × (Λ S' γ v₂)

sub-Λ : ∀{Γ}{E : Sem (Γ , ★)}{γ v v'} → (Λ E) γ v → v' ⊑ v → (Λ E) γ v'
sub-Λ γ Bot⊑ = tt
sub-Λ γ Lit⊑ = γ
sub-Λ γ Fun⊑ = γ
sub-Λ γ (ConjL⊑ lt lt₁) = ⟨ sub-Λ γ lt , sub-Λ γ lt₁ ⟩
sub-Λ γ (ConjR1⊑ lt) = sub-Λ (proj₁ γ) lt
sub-Λ γ (ConjR2⊑ lt) = sub-Λ (proj₂ γ) lt

ℒλ≃Λℒ : ∀{Γ}{M : Γ , ★ ⊢ ★} → ℒ (ƛ M) ≃ Λ (ℒ M)
ℒλ≃Λℒ {Γ}{M} = ⟨ G , H ⟩
  where G : ∀{γ v} → ℒ (ƛ M) γ v → Λ (ℒ M) γ v
        G (↦-intro d) = d
        G ⊥-intro = tt
        G (⊔-intro d₁ d₂) = ⟨ (G d₁) , (G d₂) ⟩

        H : ∀{γ v} → Λ (ℒ M) γ v → ℒ (ƛ M) γ v
        H {γ} {⊥} d = ⊥-intro
        H {γ} {lit x} ()
        H {γ} {v ↦ v'} d = ↦-intro d
        H {γ} {v₁ ⊔ v₂} ⟨ d₁ , d₂ ⟩ = ⊔-intro (H d₁) (H d₂)

app : ∀{Γ} → Sem Γ → Sem Γ → Sem Γ
app F E γ v =
   Σ[ v₁ ∈ Value ] Σ[ v₂ ∈ Value ] Σ[ v₃ ∈ Value ] Σ[ v₄ ∈ Value ]
      F γ v₁ × E γ v₂ × v₃ ↦ v₄ ⊑ v₁ × v₃ ⊑ v₂ × v ⊑ v₄

infixl 7 _●_

_●_ : ∀{Γ} → Sem Γ → Sem Γ → Sem Γ
(F ● E) γ ⊥ = app F E γ ⊥
(F ● E) γ (lit x) = app F E γ (lit x)
(F ● E) γ (v ↦ v') = app F E γ (v ↦ v')
(F ● E) γ (v₁ ⊔ v₂) = (F ● E) γ v₁ × (F ● E) γ v₂


sub-app-● : ∀{Γ}{F E : Sem Γ}{γ v v'} → app F E γ v → v' ⊑ v → (F ● E) γ v'
sub-app-● ⟨ v₁ , ⟨ v₂ , ⟨ v₃ , ⟨ v₄ , ⟨ Fv₁ , ⟨ Ev₂ , ⟨ v34⊑v1 , ⟨ v32 , vv4 ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ Bot⊑ =
  ⟨ v₁ , ⟨ v₂ , ⟨ v₃ , ⟨ v₄ , ⟨ Fv₁ , ⟨ Ev₂ , ⟨ v34⊑v1 , ⟨ v32 , Bot⊑ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩
sub-app-● ⟨ v₁ , ⟨ v₂ , ⟨ v₃ , ⟨ v₄ , ⟨ Fv₁ , ⟨ Ev₂ , ⟨ v34⊑v1 , ⟨ v32 , vv4 ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ Lit⊑ =
  ⟨ v₁ , ⟨ v₂ , ⟨ v₃ , ⟨ v₄ , ⟨ Fv₁ , ⟨ Ev₂ , ⟨ v34⊑v1 , ⟨ v32 , vv4 ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩
sub-app-● ⟨ v₁ , ⟨ v₂ , ⟨ v₃ , ⟨ v₄ , ⟨ Fv₁ , ⟨ Ev₂ , ⟨ v34⊑v1 , ⟨ v32 , vv4 ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ Fun⊑ =
  ⟨ v₁ , ⟨ v₂ , ⟨ v₃ , ⟨ v₄ , ⟨ Fv₁ , ⟨ Ev₂ , ⟨ v34⊑v1 , ⟨ v32 , vv4 ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩
sub-app-● d (ConjL⊑ lt₁ lt₂) = {!!}
sub-app-● d (ConjR1⊑ lt) = {!!}
sub-app-● d (ConjR2⊑ lt) = {!!}

sub-● : ∀{Γ}{F E : Sem Γ}{γ v v'} → (F ● E) γ v → v' ⊑ v → (F ● E) γ v'
sub-● {Γ} {F} {E} {γ} {⊥} {v'} d lt = sub-app-● d lt
sub-● {Γ} {F} {E} {γ} {lit x} {v'} d lt = sub-app-● d lt
sub-● {Γ} {F} {E} {γ} {v ↦ v₁} {v'} d lt = sub-app-● d lt
sub-● {Γ} {F} {E} {γ} {v₁ ⊔ v₂} {.⊥} ⟨ d₁ , d₂ ⟩ Bot⊑ = {!!}
sub-● {Γ} {F} {E} {γ} {v₁ ⊔ v₂} {.(_ ⊔ _)} ⟨ d₁ , d₂ ⟩ (ConjL⊑ lt lt₁) = {!!}
sub-● {Γ} {F} {E} {γ} {v₁ ⊔ v₂} {v'} ⟨ d₁ , d₂ ⟩ (ConjR1⊑ lt) = {!!}
sub-● {Γ} {F} {E} {γ} {v₁ ⊔ v₂} {v'} ⟨ d₁ , d₂ ⟩ (ConjR2⊑ lt) = {!!}



⊔⊑L : ∀{v₁ v₂ v : Value}
    → v₁ ⊔ v₂ ⊑ v
    → v₁ ⊑ v
⊔⊑L (ConjL⊑ d d₁) = d
⊔⊑L (ConjR1⊑ d) = ConjR1⊑ (⊔⊑L d)
⊔⊑L (ConjR2⊑ d) = ConjR2⊑ (⊔⊑L d)

⊔⊑R : ∀{v₁ v₂ v : Value}
    → v₁ ⊔ v₂ ⊑ v
    → v₂ ⊑ v
⊔⊑R (ConjL⊑ d d₁) = d₁
⊔⊑R (ConjR1⊑ d) = ConjR1⊑ (⊔⊑R d)
⊔⊑R (ConjR2⊑ d) = ConjR2⊑ (⊔⊑R d)


ℒ·≃●ℒ : ∀{Γ}{M N : Γ ⊢ ★} → ℒ (M · N) ≃ (ℒ M) ● (ℒ N)
ℒ·≃●ℒ {Γ}{M}{N} = ⟨ G , H ⟩
  where G : ∀{γ v} → ℒ (M · N) γ v → (ℒ M ● ℒ N) γ v
        G {γ} {v} d = {!!}

        H : ∀{γ v} → (ℒ M ● ℒ N) γ v → ℒ (M · N) γ v
        H {γ} {v} d =
           {!!}
-}
