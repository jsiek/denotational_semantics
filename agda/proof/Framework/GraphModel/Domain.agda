module proof.Framework.GraphModel.Domain where

open import Framework.GraphModel.Domain public

open import Framework.Primitives
open import proof.Framework.GraphModel.SetsAsPredicates
open import proof.Framework.GraphModel.DenotProperties
open import Framework.GraphModel.Env using (Env)

open import Data.List using (List ; _∷_ ; [])
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Relation.Unary.All using (All; []; _∷_; lookup; tabulate)
open import Data.Product using (_×_; Σ-syntax) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₂)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (tt) renaming (⊤ to True)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)

{- the environment of a closed program -}
ρ₀ : Env Value
ρ₀ = λ _ → ⌈ ω ⌉

≈⇒Every : ∀ A B → A ≈ B → Every _~_ (mem A) (mem B)
≈⇒Every (x ∷ A) B ⟨ x~B , A~B ⟩ a b (here refl) b∈B = 
  lookup x~B b∈B
≈⇒Every (x ∷ A) B ⟨ x~B , A~B ⟩ a b (there a∈A) b∈B = 
  ≈⇒Every A B A~B a b a∈A b∈B

Every⇒≈ : ∀ A B → Every _~_ (mem A) (mem B) → A ≈ B
Every⇒≈ [] B A~B = tt
Every⇒≈ (x ∷ A) B A~B = 
  ⟨ tabulate (λ {b} b∈B → A~B x b (here refl) b∈B) 
  , Every⇒≈ A B (λ a b a∈A b∈B → A~B a b (there a∈A) b∈B) ⟩


{- every value is consistent with itself -}
~-refl : ∀ v → v ~ v
~-refl (const k) = ⟨ refl , refl ⟩
~-refl (V ↦ w) = λ _ → ~-refl w
~-refl ν = tt
~-refl ω = tt
~-refl ⦅ u , v ⦆ = ⟨ ~-refl u , ~-refl v ⟩
~-refl (tup[ i ] d) = ⟨ refl , inj₂ ⟨ refl , ~-refl d ⟩ ⟩
~-refl (left d) = ~-refl d
~-refl (right d) = ~-refl d
~-refl ⟨⟩ = tt

{- consistent sets, and environments of them: the binders Λ and 𝒞 bind
   only consistent sets -}
Con : 𝒫 Value → Set
Con D = Every _~_ D D

Con-env : (ℕ → 𝒫 Value) → Set
Con-env ρ = ∀ x → Con (ρ x)

Con-• : ∀ {D ρ} → Con D → Con-env ρ → Con-env (D • ρ)
Con-• c cρ zero = c
Con-• c cρ (suc x) = cρ x

Con-⌈⌉ : ∀ v → Con ⌈ v ⌉
Con-⌈⌉ v _ _ refl refl = ~-refl v

≈⇒Con : ∀ {V} → V ≈ V → Con (mem V)
≈⇒Con {V} = ≈⇒Every V V

Con-⊆ : ∀ {D E} → Con D → E ⊆ D → Con E
Con-⊆ c E⊆ = Every-⊆ c E⊆ E⊆

Con⇒≈ : ∀ {D} V → Con D → mem V ⊆ D → V ≈ V
Con⇒≈ V c V⊆ = Every⇒≈ V V (Con-⊆ c V⊆)

≈-single : ∀ {v} → (v ∷ []) ≈ (v ∷ [])
≈-single {v} = ⟨ ~-refl v ∷ [] , tt ⟩
