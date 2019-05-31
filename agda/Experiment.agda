open import Variables
open import Structures
open import Lambda using (_·_; ƛ; Term; lam; app)
open Lambda.Reduction using (_—→_; ξ₁-rule; ξ₂-rule; β-rule; ζ-rule)
open Lambda.ASTMod
   using (`_; _⦅_⦆; Subst;
          exts; cons; bind; nil; rename; ⟪_⟫; subst-zero; _[_]; rename-id)

open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; sym; cong; cong₂; cong-app)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)
open import Data.Product using (_×_; Σ; Σ-syntax; ∃; ∃-syntax; proj₁; proj₂)
  renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥-elim) renaming (⊥ to Bot)
open import Function using (_∘_)
open import Data.Unit using (⊤; tt)
open import Data.Empty renaming (⊥ to Bot)
open import Relation.Nullary using (¬_; Dec; yes; no)

module Experiment where



module SubstPres
  (_●_ : ∀{Γ} → DenotAux.Denotation Γ → Denotation Γ → Denotation Γ)
  (MB : ModelBasics _●_)
  where



`⊥ : ∀ {Γ} → Env Γ
`⊥ x = ⊥

record ModelBot
       (_●_ : ∀{Γ} → Denotation Γ → Denotation Γ → Denotation Γ)
       : Set₁ where
  field
    MB : ModelBasics _●_
    ●-⊥ : ∀{Γ}{D₁ D₂ : Denotation Γ} {γ : Env Γ}
         → (D₁ ● D₂) γ ⊥

record ModelExtra
       (_●_ : ∀{Γ} → Denotation Γ → Denotation Γ → Denotation Γ)
       : Set₁ where
  field
    MBot : ModelBot _●_
    ●-≡ : ∀{Γ}{D₁ D₂ : Denotation Γ}{γ : Env Γ} {w : Value}
        → (D₁ ● D₂) γ w ≡ (w ⊑ ⊥ ⊎ (Σ[ v ∈ Value ] D₁ γ (v ↦ w) × D₂ γ v))
    ℱ-inv : ∀{Γ}{D : Denotation (suc Γ)}{γ : Env Γ}{u : Value}
          → ℱ D γ u
          → u ⊑ ⊥ ⊎ (Σ[ v ∈ Value ] Σ[ w ∈ Value ]
                      (D (γ `, v) w) × ((v ↦ w) ⊑ u))

