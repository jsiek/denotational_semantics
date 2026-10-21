module Untyped.proof.Semantics.GraphErr.Clos5 where

open import proof.Framework.GraphModel.SetsAsPredicates
open import proof.Framework.GraphModel.DenotProperties using (Every)
open import proof.Framework.GraphModel.Domain
open import proof.Framework.GraphModel.ContinuityBase
open import proof.Framework.GraphModel.ErrorMonad
open import proof.Semantics.GraphErr.Prim
open import Untyped.Language.Clos5
open import Untyped.Semantics.GraphErr.Clos5 public
open import proof.Framework.GraphModel.Env using (_⊆ₑ_; •-~)
open import proof.Framework.GraphModel.Semantics Op sig using (Semantics; ⟦⟧-monotone)
open import proof.Framework.GraphModel.SemanticsCore Op sig using (module GoodSemantics)

open import Data.Nat using (_≟_)
open import Relation.Nullary using (yes; no)
open import Data.List using (_∷_; []; length)
open import Level using (lift)

{- The semantics of Semantics/GraphErr/Clos5.agda, for any table T, as an
   instance of the generic Semantics record: its operators are Good, with
   consistency under a consistent table. -}

private
  good : ∀ T op → Good (∀ k → Con (T k)) (sig op) (𝕆-Clos5ᵐ T op)
  good T (fun-ref k) =
    record { mono = λ _ _ _ → lift (λ d d∈ → d∈) ; consis = λ TC _ _ _ → lift (TC k) ; cont = λ _ NE _ → const-cont NE }
  good T app = callᵐ-good
  good T (lit B k) = ℬ-good B k
  good T pair-op = pairᵐ-good
  good T fst-op = carᵐ-good
  good T snd-op = cdrᵐ-good
  good T (tuple n) = 𝒯ᵐ-good n
  good T (get i) = projᵐ-good i
  good T inl-op = inlᵐ-good
  good T inr-op = inrᵐ-good
  good T case-op = 𝒞ᵐ-good
  good T (prim p) = primᵐ-good p
  good T let-op = letᵐ-good

  module G (T : Table) = GoodSemantics (∀ k → Con (T k)) (𝕆-Clos5ᵐ T) (good T)

Clos5ᵐ-Semantics : Table → Semantics
Clos5ᵐ-Semantics T = G.Sem T

Clos5ᵐ-Continuous = G.Cont-Sem

module _ (T : Table) where
  ⟦⟧[]-monotone : ∀ (M : AST) {ρ ρ′} → ρ ⊆ₑ ρ′ → ⟦ M ⟧[ T ] ρ ⊆ ⟦ M ⟧[ T ] ρ′
  ⟦⟧[]-monotone M = ⟦⟧-monotone {{Clos5ᵐ-Semantics T}} M

  open G T public using (term-continuous; body-mono; body-continuous; body2-continuous)

{- with a consistent table and environments, denotations are consistent -}
Clos5ᵐ-con-env = G.con-env
Clos5ᵐ-con = G.con

{- the tables of programs are consistent -}
table-con : ∀ ds k → Con (table ds k)
table-con [] k = errcode-con
table-con (N ∷ Ns) k with k ≟ length Ns
... | yes _ = ΛΛᵐ-con (λ X X' Y Y' X~ Y~ →
                Clos5ᵐ-con-env (table Ns) (table-con Ns) N (•-~ (Every _~_) (•-~ (Every _~_) (λ _ → Con-⌈⌉ ω) X~) Y~))
... | no _ = table-con Ns k
