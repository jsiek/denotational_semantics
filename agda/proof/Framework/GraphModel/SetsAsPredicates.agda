module proof.Framework.GraphModel.SetsAsPredicates where

open import Framework.GraphModel.SetsAsPredicates public

open import Data.Empty renaming (⊥ to False)
open import Data.Product using (_×_; Σ; Σ-syntax; proj₁; proj₂)
    renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality
    using (_≡_; _≢_; refl; sym; subst)
open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.Any using (Any; here; there)

infix 9 _∪_
_∪_ : ∀{T : Set} → 𝒫 T → 𝒫 T → 𝒫 T
(D ∪ E) d = d ∈ D ⊎ d ∈ E

infix 9 _∩_
_∩_ : ∀{T : Set} → 𝒫 T → 𝒫 T → 𝒫 T
(D ∩ E) d = d ∈ D × d ∈ E

≃-refl : ∀{T : Set}{D : 𝒫 T} → D ≃ D
≃-refl {D} = ⟨ (λ d z → z) , (λ d z → z) ⟩

≃-reflexive : ∀{T : Set}{D₁ D₂ : 𝒫 T} → D₁ ≡ D₂ → D₁ ≃ D₂
≃-reflexive refl = ⟨ (λ d z → z) , (λ d z → z) ⟩

≃-sym : ∀{T : Set}{D₁ D₂ : 𝒫 T} → D₁ ≃ D₂ → D₂ ≃ D₁
≃-sym ⟨ t , f ⟩ = ⟨ f , t ⟩

≃-trans : ∀{T : Set}{D₁ D₂ D₃ : 𝒫 T} → D₁ ≃ D₂ → D₂ ≃ D₃ → D₁ ≃ D₃
≃-trans ⟨ d12 , d21 ⟩ ⟨ d23 , d32 ⟩ =
    ⟨ (λ d z → d23 d (d12 d z)) , (λ d z → d21 d (d32 d z)) ⟩

module ≃-Reasoning where
  infixr 2 _≃⟨⟩_
  _≃⟨⟩_ : ∀ {T : Set}(D₁ : 𝒫 T) {D₂ : 𝒫 T} → D₁ ≃ D₂ → D₁ ≃ D₂
  D₁ ≃⟨⟩ D₁≃D₂ = D₁≃D₂

  infixr 2 _≃⟨_⟩_
  _≃⟨_⟩_ : ∀ {T : Set} (D₁ : 𝒫 T) {D₂ D₃ : 𝒫 T} → D₁ ≃ D₂ → D₂ ≃ D₃ → D₁ ≃ D₃
  D₁ ≃⟨ D₁≃D₂ ⟩ D₂≃D₃ = ≃-trans D₁≃D₂ D₂≃D₃

  infix 3 _∎
  _∎ : ∀ {T : Set}(D : 𝒫 T) → D ≃ D
  D ∎  =  ≃-refl


E≢[]⇒nonempty-mem : ∀{T}{E : List T}
  → E ≢ [] → nonempty (mem E)
E≢[]⇒nonempty-mem {T} {[]} E≢[] = ⊥-elim (E≢[] refl)
E≢[]⇒nonempty-mem {T} {x ∷ E} E≢[] = ⟨ x , here refl ⟩

ne-mem : ∀ {T} {V : List T} {D : 𝒫 T} → V ≢ [] → mem V ⊆ D → nonempty D
ne-mem {V = []} ne _ = ⊥-elim (ne refl)
ne-mem {V = v ∷ V} _ V⊆ = ⟨ v , V⊆ v (here refl) ⟩

{- A ≃ B when they are equal under P and an element of either gives P -}
≃-when : ∀ {T} {P : Set} {A B : 𝒫 T} → (∀ w → w ∈ A → P) → (∀ w → w ∈ B → P)
  → (P → A ≃ B) → A ≃ B
≃-when pA pB eq = ⟨ (λ w w∈ → proj₁ (eq (pA w w∈)) w w∈) , (λ w w∈ → proj₂ (eq (pB w w∈)) w w∈) ⟩
