module Untyped.proof.Semantics.GraphErr.Clos4 where

open import proof.Framework.GraphModel.ContinuityBase using (Good; ℬ-good)
open import proof.Framework.GraphModel.ErrorMonad
open import proof.Semantics.GraphErr.Prim
open import Untyped.Language.Clos4
open import Untyped.Semantics.GraphErr.Clos4 public hiding (⟦_⟧; init)
open import proof.Framework.GraphModel.SemanticsCore Op sig using (module GoodSemantics)

open import Data.Unit using (⊤; tt)

{- The semantics of Semantics/GraphErr/Clos4.agda as an instance of the
   generic Semantics record, whose ⟦_⟧ is by definition the ⟦_⟧ there:
   its operators are Good (monotone, consistent and continuous). -}

private
  good : ∀ op → Good ⊤ (sig op) (𝕆-Clos4ᵐ op)
  good fun-op = ΛΛᵐ-good
  good app = callᵐ-good
  good (lit B k) = ℬ-good B k
  good pair-op = pairᵐ-good
  good fst-op = carᵐ-good
  good snd-op = cdrᵐ-good
  good (tuple n) = 𝒯ᵐ-good n
  good (get i) = projᵐ-good i
  good inl-op = inlᵐ-good
  good inr-op = inrᵐ-good
  good case-op = 𝒞ᵐ-good
  good (prim p) = primᵐ-good p
  good let-op = letᵐ-good

  module G = GoodSemantics ⊤ 𝕆-Clos4ᵐ good

open import proof.Framework.GraphModel.Semantics Op sig public

instance
  Clos4ᵐ-Semantics : Semantics
  Clos4ᵐ-Semantics = G.Sem
open Semantics {{...}} public

open G public using (term-continuous; body-mono; body-continuous; body2-continuous)

Clos4ᵐ-con-env = G.con-env tt
Clos4ᵐ-con = G.con tt
