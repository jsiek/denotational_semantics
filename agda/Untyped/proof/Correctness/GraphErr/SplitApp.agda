{-

  The split pass translates an application with a let,

    let f = L' in app (fst f , snd f , shift N'),

  which, in the graph model with errors, binds L' and calls each
  set of its values: L' ≫= λ X → X ⊙ N', when L' is consistent. It is
  the monad's laws: the function the let applies is a set of functions
  (⋆ᵐ-val), and it is applied to a consistent set of values (Λᵐ-β).

-}

open import Framework.Syntax.SyntaxUtil
open import proof.Framework.GraphModel.SetsAsPredicates
open import proof.Framework.GraphModel.Domain
open import proof.Framework.GraphModel.ErrorMonad
open import proof.Framework.GraphModel.ContinuityBase using (mono)
open import proof.Framework.GraphModel.OpsBase using (mono-≃)
open import proof.Framework.GraphModel.Ops using (⋆)
open import Untyped.Language.Clos4
open import proof.Framework.Syntax.Rename Op sig using (shift)
open import Untyped.proof.Semantics.GraphErr.Clos4
open import proof.Framework.GraphModel.RenameSem Op sig using (shift-≃)
open import proof.Framework.GraphModel.Env using (Env; nonempty-env)
open import Untyped.proof.Correctness.GraphErr.SplitRel using (_⊙_)

open import Data.Product using (proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Unit using (tt; ⊤)
open import Data.Unit.Polymorphic using () renaming (tt to ptt)
open import Level using (lift)

module Untyped.proof.Correctness.GraphErr.SplitApp where

let-app : AST → AST → AST
let-app L' N' =
  let-op ⦅ L' ,, ⟩ (app ⦅ (fst-op ⦅ (` 0) ,, Nil ⦆) ,, (snd-op ⦅ (` 0) ,, Nil ⦆) ,,
                          shift N' ,, Nil ⦆) ,, Nil ⦆

let-app-≃ : ∀ (L' N' : AST) (ρ : Env Value) → nonempty-env ρ → Con (⟦ L' ⟧ ρ)
  → ⟦ let-app L' N' ⟧ ρ ≃ (⟦ L' ⟧ ρ ≫= λ X → X ⊙ ⟦ N' ⟧ ρ)
let-app-≃ L' N' ρ NE cL =
  ≃-trans (⋆ᵐ-val {Λᵐ ⟨ F , ptt ⟩} {⟦ L' ⟧ ρ} Λᵐ-clean ⟨ ν , ⟨ tt , tt ⟩ ⟩ Λᵐ-fun)
          (≫=-cong {⟦ L' ⟧ ρ} {λ X → ⋆ ⟨ Λᵐ ⟨ F , ptt ⟩ , ⟨ X , ptt ⟩ ⟩} {λ X → X ⊙ ⟦ N' ⟧ ρ} λ { ⟨ d , d∈ ⟩ →
             ≃-trans (Λᵐ-β (body-mono B ρ) (body-continuous B ρ NE _ ⟨ d , d∈ ⟩) (Con-⊆ cL ⌊⌋-⊆) (λ e e∈ → proj₂ e∈))
                     (mono-≃ (mono (callᵐ-good {⊤})) ⟨ lift ≃-refl , ⟨ lift ≃-refl , ⟨ lift (shift-≃ N' _ ρ) , ptt ⟩ ⟩ ⟩) })
  where
  B = app ⦅ (fst-op ⦅ (` 0) ,, Nil ⦆) ,, (snd-op ⦅ (` 0) ,, Nil ⦆) ,, shift N' ,, Nil ⦆
  F = λ X → ⟦ B ⟧ (X • ρ)
