module proof.Semantics.Graph.ISWIM where

open import proof.Framework.GraphModel.Continuity
open import proof.Semantics.Graph.Prim
open import Language.ISWIM
open import Semantics.Graph.ISWIM public hiding (⟦_⟧; init)
open import proof.Framework.GraphModel.SemanticsUtil Op sig using (module GoodSemantics)

open import Data.Unit using (⊤; tt)

{- The semantics of Semantics/Graph/ISWIM.agda as an instance of the
   generic Semantics record (proof/Framework/GraphModel/Semantics.agda),
   whose ⟦_⟧ is by definition the ⟦_⟧ there: its operators are Good. -}

private
  good : ∀ op → Good ⊤ (sig op) (𝕆-ISWIM op)
  good lam = Λ-good
  good app = ⋆-good
  good (lit B k) = ℬ-good B k
  good (tuple n) = 𝒯-good n
  good (get i) = proj-good i
  good inl-op = inl-good
  good inr-op = inr-good
  good case-op = 𝒞-good
  good (prim p) = primD-good p
  good let-op = letD-good

  module G = GoodSemantics ⊤ 𝕆-ISWIM good

open import proof.Framework.GraphModel.Semantics Op sig public

instance
  ISWIM-Semantics : Semantics
  ISWIM-Semantics = G.Sem
open Semantics {{...}} public

ISWIM-Continuous : ContinuousSemantics
ISWIM-Continuous = G.Cont-Sem

open G public using (term-continuous; body-mono; body-continuous; let-β)

{- consistent environments give consistent denotations -}
ISWIM-con-env = G.con-env tt
