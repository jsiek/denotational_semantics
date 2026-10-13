module proof.Semantics.GraphErr.Clos3 where

open import proof.Framework.GraphModel.ContinuityBase using (Good; ℬ-good)
open import proof.Framework.GraphModel.ErrorContinuity
open import proof.Semantics.GraphErr.Prim
open import Language.Clos3
open import Semantics.GraphErr.Clos3 public hiding (⟦_⟧; init)
open import proof.Framework.GraphModel.SemanticsCore Op sig using (module GoodSemantics)

open import Data.Unit using (⊤; tt)

{- The semantics of Semantics/GraphErr/Clos3.agda as an instance of the
   generic Semantics record, whose ⟦_⟧ is by definition the ⟦_⟧ there:
   its operators are Good (monotone, consistent and continuous). -}

private
  good : ∀ op → Good ⊤ (sig op) (𝕆-Clos3ᵉ op)
  good (clos-op n) = closᵉ-good n
  good app = ⋆ᵉ-good
  good (lit B k) = ℬ-good B k
  good (tuple n) = 𝒯ᵉ-good n
  good (get i) = projᵉ-good i
  good inl-op = inlᵉ-good
  good inr-op = inrᵉ-good
  good case-op = 𝒞ᵉ-good
  good (prim p) = primᵉ-good p
  good let-op = letᵉ-good

  module G = GoodSemantics ⊤ 𝕆-Clos3ᵉ good

open import proof.Framework.GraphModel.Semantics Op sig public

instance
  Clos3ᵉ-Semantics : Semantics
  Clos3ᵉ-Semantics = G.Sem
open Semantics {{...}} public

open G public using (term-continuous; body-mono; body-continuous; body2-continuous)

Clos3ᵉ-con-env = G.con-env tt
Clos3ᵉ-con = G.con tt
