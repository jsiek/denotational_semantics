module Untyped.proof.Semantics.GraphErr.Clos3 where

open import proof.Framework.GraphModel.ContinuityBase using (Good; ℬ-good)
open import proof.Framework.GraphModel.ErrorMonad
open import proof.Semantics.GraphErr.Prim
open import Untyped.Language.Clos3
open import Untyped.Semantics.GraphErr.Clos3 public hiding (⟦_⟧; init)
open import proof.Framework.GraphModel.SemanticsCore Op sig using (module GoodSemantics)

open import Data.Unit using (⊤; tt)

{- The semantics of Semantics/GraphErr/Clos3.agda as an instance of the
   generic Semantics record, whose ⟦_⟧ is by definition the ⟦_⟧ there:
   its operators are Good (monotone, consistent and continuous). -}

private
  good : ∀ op → Good ⊤ (sig op) (𝕆-Clos3ᵐ op)
  good (clos-op n) = closᵐ-good n
  good app = ⋆ᵐ-good
  good (lit B k) = ℬ-good B k
  good (tuple n) = 𝒯ᵐ-good n
  good (get i) = projᵐ-good i
  good inl-op = inlᵐ-good
  good inr-op = inrᵐ-good
  good case-op = 𝒞ᵐ-good
  good (prim p) = primᵐ-good p
  good let-op = letᵐ-good

  module G = GoodSemantics ⊤ 𝕆-Clos3ᵐ good

open import proof.Framework.GraphModel.Semantics Op sig public

instance
  Clos3ᵐ-Semantics : Semantics
  Clos3ᵐ-Semantics = G.Sem
open Semantics {{...}} public

open G public using (term-continuous; body-mono; body-continuous; body2-continuous)

Clos3ᵐ-con-env = G.con-env tt
Clos3ᵐ-con = G.con tt
