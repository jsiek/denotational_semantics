{-

  Definitions shared by the proofs for the split pass (SplitPreserve,
  SplitFiniteRel, SplitReflectFinite) and the other passes: operator
  shorthands, environments, and the facts about values and finite sets of
  them (proof/Framework/GraphModel/DomainUtil.agda).

-}

open import proof.Framework.GraphModel.SetsAsPredicates
open import proof.Framework.GraphModel.Domain
open import proof.Framework.GraphModel.Ops
open import proof.Semantics.Graph.Prim
import proof.Framework.GraphModel.Env

open import Data.Product using (_×_) renaming (_,_ to ⟨_,_⟩ )
open import Data.Unit.Polymorphic using () renaming (tt to ptt)
open import Data.Bool using (true; false)
open import Language.Prim using (int; bool)

module Untyped.proof.Correctness.Graph.SplitFiniteCommon where

open import proof.Framework.GraphModel.DomainUtil public

{- Shorthands ----------------------------------------------------------------}

Env : Set₁
Env = proof.Framework.GraphModel.Env.Env Value

_●_ : 𝒫 Value → 𝒫 Value → 𝒫 Value
D ● E = ⋆ ⟨ D , ⟨ E , ptt ⟩ ⟩

Car : 𝒫 Value → 𝒫 Value
Car D = car ⟨ D , ptt ⟩

Cdr : 𝒫 Value → 𝒫 Value
Cdr D = cdr ⟨ D , ptt ⟩

{- application of a target closure: (car D ⋆ cdr D) ⋆ E -}
_⊙_ : 𝒫 Value → 𝒫 Value → 𝒫 Value
D ⊙ E = (Car D ● Cdr D) ● E

Init : 𝒫 Value
Init = ⌈ ω ⌉

open proof.Framework.GraphModel.Domain using (ρ₀) public
open proof.Framework.GraphModel.SetsAsPredicates using (ne-mem) public

●-mono-l : ∀ {D₁ D₂ E} → D₁ ⊆ D₂ → (D₁ ● E) ⊆ (D₂ ● E)
●-mono-l D⊆ w ⟨ V , ⟨ V↦w∈ , ⟨ V⊆E , neV ⟩ ⟩ ⟩ = ⟨ V , ⟨ D⊆ _ V↦w∈ , ⟨ V⊆E , neV ⟩ ⟩ ⟩

Cdr-mono : ∀ {D₁ D₂} → D₁ ⊆ D₂ → Cdr D₁ ⊆ Cdr D₂
Cdr-mono D⊆ v ⟨ u , uv∈ ⟩ = ⟨ u , D⊆ _ uv∈ ⟩

⊙-mono-l : ∀ {D₁ D₂ E} → D₁ ⊆ D₂ → (D₁ ⊙ E) ⊆ (D₂ ⊙ E)
⊙-mono-l D⊆ w ⟨ U , ⟨ ⟨ FV , ⟨ ⟨ t , f∈ ⟩ , ⟨ FV⊆ , neFV ⟩ ⟩ ⟩ , ⟨ U⊆ , neU ⟩ ⟩ ⟩ =
  ⟨ U , ⟨ ⟨ FV , ⟨ ⟨ t , D⊆ _ f∈ ⟩ , ⟨ (λ d d∈ → Cdr-mono D⊆ d (FV⊆ d d∈)) , neFV ⟩ ⟩ ⟩
        , ⟨ U⊆ , neU ⟩ ⟩ ⟩

{- the results of the primitives are first-order data -}
out-data : ∀ o → Data (out o)
out-data (int n) = flat-const
out-data (bool true) = flat-⟨⟩
out-data (bool false) = flat-⟨⟩
