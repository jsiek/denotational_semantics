module Untyped.proof.Semantics.Graph.Clos4Iswim where

open import proof.Framework.GraphModel.Continuity
open import proof.Semantics.Graph.Prim
open import Untyped.Language.Clos4
open import Untyped.Semantics.Graph.Clos4Iswim public hiding (⟦_⟧; init)
open import proof.Framework.GraphModel.SemanticsUtil Op sig using (module GoodSemantics)

open import Data.Unit using (⊤; tt)

{- The semantics of Semantics/Graph/Clos4Iswim.agda as an instance of
   the generic Semantics record (proof/Framework/GraphModel/Semantics.agda),
   whose ⟦_⟧ is by definition the ⟦_⟧ there: its operators are Good. -}

private
  good : ∀ op → Good ⊤ (sig op) (𝕆-Clos4 op)
  good fun-op = ΛΛ-good
  good app = ⋆₂-good
  good (lit B k) = ℬ-good B k
  good pair-op = pair-good
  good fst-op = car-good
  good snd-op = cdr-good
  good (tuple n) = 𝒯-good n
  good (get i) = proj-good i
  good inl-op = inl-good
  good inr-op = inr-good
  good case-op = 𝒞-good
  good (prim p) = primD-good p
  good let-op = letD-good

  module G = GoodSemantics ⊤ 𝕆-Clos4 good

open import proof.Framework.GraphModel.Semantics Op sig public

instance
  Clos4-Semantics : Semantics
  Clos4-Semantics = G.Sem
open Semantics {{...}} public

Clos4-Continuous : ContinuousSemantics
Clos4-Continuous = G.Cont-Sem

open G public using (term-continuous; body-mono; body-continuous; body2-continuous; let-β; clos-β)

{- a consistent environment gives a consistent denotation -}
Clos4-con = G.con tt
