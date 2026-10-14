module Untyped.proof.Semantics.Graph.Clos3Iswim where

open import proof.Framework.GraphModel.Continuity
open import proof.Semantics.Graph.Prim
open import Untyped.Language.Clos3
open import Untyped.Semantics.Graph.Clos3Iswim public hiding (⟦_⟧; init)
open import proof.Framework.GraphModel.SemanticsUtil Op sig using (module GoodSemantics)

open import Data.Unit using (⊤; tt)

{- The semantics of Semantics/Graph/Clos3Iswim.agda as an instance of
   the generic Semantics record (proof/Framework/GraphModel/Semantics.agda),
   whose ⟦_⟧ is by definition the ⟦_⟧ there: its operators are Good. -}

private
  good : ∀ op → Good ⊤ (sig op) (𝕆-Clos3 op)
  good (clos-op n) = closD-good n
  good app = ⋆-good
  good (lit B k) = ℬ-good B k
  good (tuple n) = 𝒯-good n
  good (get i) = proj-good i
  good inl-op = inl-good
  good inr-op = inr-good
  good case-op = 𝒞-good
  good (prim p) = primD-good p
  good let-op = letD-good

  module G = GoodSemantics ⊤ 𝕆-Clos3 good

open import proof.Framework.GraphModel.Semantics Op sig public

instance
  Clos3-Semantics : Semantics
  Clos3-Semantics = G.Sem
open Semantics {{...}} public

Clos3-Continuous : ContinuousSemantics
Clos3-Continuous = G.Cont-Sem

open G public using (term-continuous; body-mono; body-continuous; body2-continuous; let-β; clos-β)

{- a consistent environment gives a consistent denotation -}
Clos3-con = G.con tt
