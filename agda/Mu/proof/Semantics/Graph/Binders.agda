{-

  Congruences of the binders of the graph model, in the form the
  correctness proofs of ISWIMμ's passes use them.

  The congruences of Ops.agda compare the bodies F and F' of a binder on
  the finite sets mem V it binds, so Agda cannot infer F from F (mem V),
  and each use names the bodies. Here the bodies are compared on every
  nonempty consistent set X (Body-≃), so F X is a pattern, and Agda
  infers F and F' from the equation that compares them. An equation also
  carries nonemptiness across (ne-≃), a strict closure's guard holds
  once its sets are nonempty (guard-yes), and the body of a term whose
  meaning is Ok is monotone in the set its binder binds (body-mono), as
  the graph laws (Λ-β, let-law, case-law) ask.

-}

module Mu.proof.Semantics.Graph.Binders where

open import proof.Framework.GraphModel.Prelude
open import proof.Framework.GraphModel.Ops
open import proof.Framework.GraphModel.Env using (•-~)
open import proof.Framework.GraphModel.TypedOkBase using (Ok)

open import Data.List using (_∷_; replicate)
open import Data.List.Relation.Unary.Any using (here)
open import Data.Product using (proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Unit.Polymorphic using () renaming (tt to ptt)
open import Relation.Binary.PropositionalEquality using (refl)

{- the bodies F and F' agree on the sets a binder binds -}
Body-≃ : (𝒫 Value → 𝒫 Value) → (𝒫 Value → 𝒫 Value) → Set₁
Body-≃ F F' = ∀ X → nonempty X → Con X → F X ≃ F' X

lam-≃ : ∀ {F F'} → Body-≃ F F' → Λ ⟨ F , ptt ⟩ ≃ Λ ⟨ F' , ptt ⟩
lam-≃ eq = Λ-≃ λ V ne c → eq (mem V) (E≢[]⇒nonempty-mem ne) (≈⇒Con c)

let-≃ : ∀ {D D' F F'} → D ≃ D' → Body-≃ F F' → letD ⟨ D , ⟨ F , ptt ⟩ ⟩ ≃ letD ⟨ D' , ⟨ F' , ptt ⟩ ⟩
let-≃ D≃ eq = ⋆-≃ (lam-≃ eq) D≃

case-≃ : ∀ {D D' F F' G G'} → D ≃ D' → Body-≃ F F' → Body-≃ G G'
  → 𝒞 ⟨ D , ⟨ F , ⟨ G , ptt ⟩ ⟩ ⟩ ≃ 𝒞 ⟨ D' , ⟨ F' , ⟨ G' , ptt ⟩ ⟩ ⟩
case-≃ {F = F} {F'} {G} {G'} D≃ F≃ G≃ =
  𝒞-≃ {F = F} {F'} {G} {G'} D≃ (λ v V c → F≃ _ ⟨ v , here refl ⟩ (≈⇒Con c)) (λ v V c → G≃ _ ⟨ v , here refl ⟩ (≈⇒Con c))

{- an equation carries nonemptiness -}
ne-≃ : ∀ {T} {D E : 𝒫 T} → D ≃ E → nonempty D → nonempty E
ne-≃ D≃ ⟨ d , d∈ ⟩ = ⟨ d , proj₁ D≃ d d∈ ⟩

{- a strict closure's guard, once its sets are nonempty -}
guard-yes : ∀ {n} {Ds : Results (𝒫 Value) (replicate n ■)} {D} → (∀ i → nonempty (nthD Ds i)) → guard-n n Ds D ≃ D
guard-yes ne = ⟨ (λ w w∈ → proj₂ w∈) , (λ w w∈ → ⟨ ne , w∈ ⟩) ⟩

{- the body of an Ok meaning is monotone in the set its binder binds -}
body-mono : ∀ {E} → Ok E → ∀ ρ {X X'} → X ⊆ X' → E (X • ρ) ⊆ E (X' • ρ)
body-mono o ρ X⊆ = proj₁ o (•-~ _⊆_ (λ _ _ z → z) X⊆)
