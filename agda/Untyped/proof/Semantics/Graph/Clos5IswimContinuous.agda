{-

  The Clos5 semantics, for a fixed table T of global definitions, is
  monotone and continuous in the environment, and consistent when the
  table is: its operators are Good (a reference to a global definition is
  a constant).

  Used by the correctness of remove complex operands
  (Correctness/RCOCorrect.agda), for the let laws, and by the soundness
  of the Clos5 machine (proof/Adequacy/Clos5Soundness.agda), for
  the steps that pass values to code (calls, case, let).

-}

module Untyped.proof.Semantics.Graph.Clos5IswimContinuous where

open import proof.Framework.GraphModel.SetsAsPredicates
open import proof.Framework.GraphModel.DenotProperties using (Every)
open import proof.Framework.GraphModel.Domain
open import proof.Framework.GraphModel.Ops using (ΛΛ-con)
open import proof.Framework.GraphModel.Continuity
open import proof.Semantics.Graph.Prim
open import Untyped.Language.Clos5
open import Untyped.Semantics.Graph.Clos5Iswim using (Table; 𝕆-Clos5; ⟦_⟧[_]; table)
open import proof.Framework.GraphModel.Env using (_⊆ₑ_; •-~)
open import proof.Framework.GraphModel.Semantics Op sig using (Semantics; ⟦⟧-monotone)
open import proof.Framework.GraphModel.SemanticsUtil Op sig using (module GoodSemantics)

open import Data.Nat using (_≟_)
open import Relation.Nullary using (yes; no)
open import Data.List using (_∷_; []; length)
open import Level using (lift)

private
  good : ∀ T op → Good (∀ k → Con (T k)) (sig op) (𝕆-Clos5 T op)
  good T (fun-ref k) =
    record { mono = λ _ _ _ → lift (λ d d∈ → d∈) ; consis = λ TC _ _ _ → lift (TC k) ; cont = λ _ NE _ → const-cont NE }
  good T app = ⋆₂-good
  good T (lit B k) = ℬ-good B k
  good T pair-op = pair-good
  good T fst-op = car-good
  good T snd-op = cdr-good
  good T (tuple n) = 𝒯-good n
  good T (get i) = proj-good i
  good T inl-op = inl-good
  good T inr-op = inr-good
  good T case-op = 𝒞-good
  good T (prim p) = primD-good p
  good T let-op = letD-good

  module G (T : Table) = GoodSemantics (∀ k → Con (T k)) (𝕆-Clos5 T) (good T)

{- ⟦ M ⟧[ T ] is the meaning of M in this semantics -}
Clos5-Semantics : Table → Semantics
Clos5-Semantics T = G.Sem T

module _ (T : Table) where
  ⟦⟧[]-monotone : ∀ (M : AST) {ρ ρ′} → ρ ⊆ₑ ρ′ → ⟦ M ⟧[ T ] ρ ⊆ ⟦ M ⟧[ T ] ρ′
  ⟦⟧[]-monotone M = ⟦⟧-monotone {{Clos5-Semantics T}} M

  open G T public using (term-continuous; let-β)

{- with a consistent table and environments, denotations are consistent -}
Clos5-con-env = G.con-env
Clos5-con = G.con

{- the tables of programs are consistent -}
table-con : ∀ ds k → Con (table ds k)
table-con [] k = λ _ _ ()
table-con (N ∷ Ns) k with k ≟ length Ns
... | yes _ = ΛΛ-con (λ X X' Y Y' X~ Y~ →
                Clos5-con-env (table Ns) (table-con Ns) N (•-~ (Every _~_) (•-~ (Every _~_) (λ _ → Con-⌈⌉ ω) X~) Y~))
... | no _ = table-con Ns k
