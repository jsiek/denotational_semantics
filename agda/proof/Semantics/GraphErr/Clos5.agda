module proof.Semantics.GraphErr.Clos5 where

open import proof.Framework.GraphModel.SetsAsPredicates
open import proof.Framework.GraphModel.DenotProperties using (Every)
open import proof.Framework.GraphModel.Domain
open import proof.Framework.GraphModel.ContinuityBase
open import proof.Framework.GraphModel.ErrorOps using (ΛΛᵉ-con; errcode-con)
open import proof.Framework.GraphModel.ErrorContinuity
open import proof.Semantics.GraphErr.Prim
open import Language.Clos5
open import Semantics.GraphErr.Clos5 public
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
  good : ∀ T op → Good (∀ k → Con (T k)) (sig op) (𝕆-Clos5ᵉ T op)
  good T (fun-ref k) =
    record { mono = λ _ _ _ → lift (λ d d∈ → d∈) ; consis = λ TC _ _ _ → lift (TC k) ; cont = λ _ NE _ → const-cont NE }
  good T app = callᵉ-good
  good T (lit B k) = ℬ-good B k
  good T pair-op = pairᵉ-good
  good T fst-op = carᵉ-good
  good T snd-op = cdrᵉ-good
  good T (tuple n) = 𝒯ᵉ-good n
  good T (get i) = projᵉ-good i
  good T inl-op = inlᵉ-good
  good T inr-op = inrᵉ-good
  good T case-op = 𝒞ᵉ-good
  good T (prim p) = primᵉ-good p
  good T let-op = letᵉ-good

  module G (T : Table) = GoodSemantics (∀ k → Con (T k)) (𝕆-Clos5ᵉ T) (good T)

Clos5ᵉ-Semantics : Table → Semantics
Clos5ᵉ-Semantics T = G.Sem T

Clos5ᵉ-Continuous = G.Cont-Sem

module _ (T : Table) where
  ⟦⟧[]-monotone : ∀ (M : AST) {ρ ρ′} → ρ ⊆ₑ ρ′ → ⟦ M ⟧[ T ] ρ ⊆ ⟦ M ⟧[ T ] ρ′
  ⟦⟧[]-monotone M = ⟦⟧-monotone {{Clos5ᵉ-Semantics T}} M

  open G T public using (term-continuous; body-mono; body-continuous; body2-continuous)

{- with a consistent table and environments, denotations are consistent -}
Clos5ᵉ-con-env = G.con-env
Clos5ᵉ-con = G.con

{- the tables of programs are consistent -}
table-con : ∀ ds k → Con (table ds k)
table-con [] k = errcode-con
table-con (N ∷ Ns) k with k ≟ length Ns
... | yes _ = ΛΛᵉ-con (λ X X' Y Y' X~ Y~ →
                Clos5ᵉ-con-env (table Ns) (table-con Ns) N (•-~ (Every _~_) (•-~ (Every _~_) (λ _ → Con-⌈⌉ ω) X~) Y~))
... | no _ = table-con Ns k
