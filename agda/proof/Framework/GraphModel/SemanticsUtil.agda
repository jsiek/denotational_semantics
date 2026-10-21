{-

  The properties of whole terms of the graph model: those of any
  graph-model semantics (SemanticsCore.agda), and the β laws of its
  binders on bodies of terms (let-β, clos-β).

-}

open import proof.Framework.GraphModel.SetsAsPredicates
open import proof.Framework.GraphModel.DOpSig
open import proof.Framework.GraphModel.Domain
open import proof.Framework.GraphModel.Ops using (ΛΛ; letD; Λ-β; ΛΛ-β; ⋆)
open import proof.Framework.GraphModel.Continuity using (Good)
open import proof.Framework.GraphModel.Env using (Env; nonempty-env)

open import Data.List using (List)
open import Data.Unit.Polymorphic using () renaming (tt to ptt)
open import Data.Product using () renaming (_,_ to ⟨_,_⟩)

module proof.Framework.GraphModel.SemanticsUtil (Op : Set) (sig : Op → List Sig) where

open import Framework.abt.AbstractBindingTree Op sig
open import proof.Framework.GraphModel.Semantics Op sig
import proof.Framework.GraphModel.SemanticsCore Op sig as Core

module Laws (C : ContinuousSemantics {Value}) where
  open Core.Laws C public
  private
    S = ContinuousSemantics.Sem C
    ⟦_⟧ = Semantics.⟦_⟧ S

  {- let x = D in N means N with D for x -}
  let-β : ∀ (N : ABT) ρ D → nonempty-env ρ → nonempty D → Con D
    → letD ⟨ D , ⟨ (λ X → ⟦ N ⟧ (X • ρ)) , ptt ⟩ ⟩ ≃ ⟦ N ⟧ (D • ρ)
  let-β N ρ D NE neD cD = Λ-β (body-mono N ρ) (body-continuous N ρ NE D neD) cD

  {- a closure applied to its environment T and to E contains its body -}
  clos-β : ∀ (N : ABT) {ρ T E} → nonempty-env ρ → nonempty T → nonempty E → Con T → Con E
    → ⟦ N ⟧ (E • T • ρ) ⊆ ⋆ ⟨ ⋆ ⟨ ΛΛ ⟨ (λ X Y → ⟦ N ⟧ (Y • X • ρ)) , ptt ⟩ , ⟨ T , ptt ⟩ ⟩ , ⟨ E , ptt ⟩ ⟩
  clos-β N {ρ} NE neT neE cT cE = ΛΛ-β {λ X Y → ⟦ N ⟧ (Y • X • ρ)} cT cE (body2-continuous N ρ NE neT neE)


module GoodSemantics (P : Set) (𝕆 : DOpSig (𝒫 Value) sig) (good : ∀ op → Good P (sig op) (𝕆 op)) where
  open Core.GoodSemantics P 𝕆 good public
  open Laws Cont-Sem public using (let-β; clos-β)
