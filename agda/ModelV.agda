open import Structures
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Product using (_×_; Σ; Σ-syntax; ∃; ∃-syntax; proj₁; proj₂)
  renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; cong; cong₂; cong-app)

import LambdaV
open LambdaV.ASTMod using (Var; Z; S_; extensionality)

module ModelV where

infixr 7 _↦_
infixl 5 _⊔_

data Value : Set where
  ⊥ : Value
  _↦_ : Value → Value → Value
  _⊔_ : Value → Value → Value

infix 4 _⊑_

data _⊑_ : Value → Value → Set where

  Bot⊑ : ∀ {v} → ⊥ ⊑ v

  ConjL⊑ : ∀ {u v w}
      → v ⊑ u
      → w ⊑ u
        -----------
      → (v ⊔ w) ⊑ u

  ConjR1⊑ : ∀ {u v w}
     → u ⊑ v
       -----------
     → u ⊑ (v ⊔ w)

  ConjR2⊑ : ∀ {u v w}
     → u ⊑ w
       -----------
     → u ⊑ (v ⊔ w)

  Trans⊑ : ∀ {u v w}
     → u ⊑ v
     → v ⊑ w
       -----
     → u ⊑ w

  Fun⊑ : ∀ {v w v′ w′}
       → v′ ⊑ v
       → w ⊑ w′
         -------------------
       → (v ↦ w) ⊑ (v′ ↦ w′)

  Dist⊑ : ∀{v w w′}
         ---------------------------------
       → v ↦ (w ⊔ w′) ⊑ (v ↦ w) ⊔ (v ↦ w′)

Refl⊑ : ∀ {v} → v ⊑ v
Refl⊑ {⊥} = Bot⊑
Refl⊑ {v ↦ v′} = Fun⊑ Refl⊑ Refl⊑
Refl⊑ {v₁ ⊔ v₂} = ConjL⊑ (ConjR1⊑ Refl⊑) (ConjR2⊑ Refl⊑)

module LM = LambdaModelMod Value _⊑_ _⊔_
open LM

ℱ : ∀{Γ} → Denotation (suc Γ) → Denotation Γ
ℱ {Γ} ⟨ D , ⟨ up-env , ⟨ down-closed , ⊔-closed ⟩ ⟩ ⟩ =
   ⟨ F ,
   ⟨ (λ {γ}{δ}{v} x x₁ → up-F {γ}{δ}{v} x x₁ ) ,
   ⟨ sub-F ,
     (λ {γ}{u}{v} x x₁ → F-⊔{γ}{u}{v} x x₁) ⟩ ⟩ ⟩
   where
   F : Env Γ → Value → Set
   F γ (v ↦ w) = D (γ `, v) w
   F γ ⊥ = ⊤
   F γ (u ⊔ v) = (F γ u) × (F γ v)

   up-F : ∀ {γ δ : Env Γ} {v : Value} →
        F γ v → ((x : Var Γ) → γ x ⊑ δ x) → F δ v
   up-F {v = ⊥} Fγv γ⊑δ = tt
   up-F {γ}{δ} {v = v ↦ w} Fγv γ⊑δ =
      up-env Fγv b
      where b : (γ `, v) `⊑ (δ `, v)
            b Z = Refl⊑
            b (S x) = γ⊑δ x

   up-F {v = u ⊔ v} ⟨ fst , snd ⟩ γ⊑δ =
      ⟨ up-F{v = u} fst γ⊑δ , up-F{v = v} snd γ⊑δ ⟩

   sub-F : {γ : Env  Γ} {v w : Value} → F γ v → w ⊑ v → F γ w
   sub-F Fγv Bot⊑ = tt
   sub-F Fγv (ConjL⊑ wv wv₁) = ⟨ (sub-F Fγv wv) , (sub-F Fγv wv₁) ⟩
   sub-F Fγv (ConjR1⊑ wv) = sub-F (proj₁ Fγv) wv
   sub-F Fγv (ConjR2⊑ wv) = sub-F (proj₂ Fγv) wv
   sub-F Fγv (Trans⊑ wv wv₁) = sub-F (sub-F Fγv wv₁) wv
   sub-F {γ}{v ↦ w}{v' ↦ w'} Fγv (Fun⊑ wv wv₁) =
      let a = up-env Fγv b in
      down-closed a wv₁
      where b : (γ `, v) `⊑ (γ `, v')
            b Z = wv
            b (S x) = Refl⊑ 
   sub-F ⟨ fst , snd ⟩ Dist⊑ = ⊔-closed fst snd

   F-⊔ : ∀{γ : Env Γ} {u v : Value} → F γ u → F γ v → F γ u × F γ v
   F-⊔ d1 d2 = ⟨ d1 , d2 ⟩

{-
infixl 7 _●_

_●_ : ∀{Γ} → Denotation Γ Value → Denotation Γ Value → Denotation Γ Value
(D₁ ● D₂) γ w = w ⊑ ⊥ ⊎ Σ[ v ∈ Value ]( D₁ γ (v ↦ w) × D₂ γ v )

sub-ℱ : ∀{Γ}{D}{γ v u}
      → ℱ {Γ} D γ v
      → u ⊑ v
        ------------
      → ℱ D γ u
sub-ℱ d Bot⊑ = tt
sub-ℱ d (Fun⊑ lt lt′) = {!!}
sub-ℱ d (ConjL⊑ lt lt₁) = ⟨ sub-ℱ d lt , sub-ℱ d lt₁ ⟩
sub-ℱ d (ConjR1⊑ lt) = sub-ℱ (proj₁ d) lt
sub-ℱ d (ConjR2⊑ lt) = sub-ℱ (proj₂ d) lt
sub-ℱ {v = v₁ ↦ v₂ ⊔ v₁ ↦ v₃} {v₁ ↦ (v₂ ⊔ v₃)} ⟨ N2 , N3 ⟩ Dist⊑ =
   {!!}
sub-ℱ d (Trans⊑ x₁ x₂) = sub-ℱ (sub-ℱ d x₂) x₁

_≃_ : ∀ {Γ} → (Denotation Γ Value) → (Denotation Γ Value) → Set
(_≃_ {Γ} D₁ D₂) = (γ : Env Γ Value) → (v : Value) → D₁ γ v iff D₂ γ v

≃-refl : ∀ {Γ} → {M : Denotation Γ Value}
  → M ≃ M
≃-refl γ v = ⟨ (λ x → x) , (λ x → x) ⟩

≃-sym : ∀ {Γ} → {M N : Denotation Γ Value}
  → M ≃ N
    -----
  → N ≃ M
≃-sym eq γ v = ⟨ (proj₂ (eq γ v)) , (proj₁ (eq γ v)) ⟩

≃-trans : ∀ {Γ} → {M₁ M₂ M₃ : Denotation Γ Value}
  → M₁ ≃ M₂
  → M₂ ≃ M₃
    -------
  → M₁ ≃ M₃
≃-trans eq1 eq2 γ v = ⟨ (λ z → proj₁ (eq2 γ v) (proj₁ (eq1 γ v) z)) ,
                        (λ z → proj₂ (eq1 γ v) (proj₂ (eq2 γ v) z)) ⟩

model : LambdaModel Value
model = record { ℱ = ℱ ;
                 _●_ = _●_ ;
                 _⊑_ = _⊑_ ;
                 Trans⊑ = Trans⊑
                 }
-}
