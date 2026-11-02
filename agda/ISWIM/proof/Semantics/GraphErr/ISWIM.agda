module proof.Semantics.GraphErr.ISWIM where

open import proof.Framework.GraphModel.ContinuityBase using (Good; ℬ-good)
open import proof.Framework.GraphModel.ErrorMonad
open import proof.Semantics.GraphErr.Prim
open import Language.ISWIM
open import Semantics.GraphErr.ISWIM public hiding (⟦_⟧; init)
open import proof.Framework.GraphModel.SemanticsCore Op sig using (module GoodSemantics)

open import Data.Unit using (⊤; tt)

{- The semantics of Semantics/GraphErr/ISWIM.agda as an instance of the
   generic Semantics record: its operators are Good. -}

private
  good : ∀ op → Good ⊤ (sig op) (𝕆-ISWIMᵐ op)
  good lam = Λᵐ-good
  good app = ⋆ᵐ-good
  good (lit B k) = ℬ-good B k
  good (tuple n) = 𝒯ᵐ-good n
  good (get i) = projᵐ-good i
  good inl-op = inlᵐ-good
  good inr-op = inrᵐ-good
  good case-op = 𝒞ᵐ-good
  good (prim p) = primᵐ-good p
  good let-op = letᵐ-good

  module G = GoodSemantics ⊤ 𝕆-ISWIMᵐ good

open import proof.Framework.GraphModel.Semantics Op sig public

instance
  ISWIMᵐ-Semantics : Semantics
  ISWIMᵐ-Semantics = G.Sem
open Semantics {{...}} public

ISWIMᵐ-Continuous : ContinuousSemantics
ISWIMᵐ-Continuous = G.Cont-Sem

open G public using (term-continuous; body-mono; body-continuous)

ISWIMᵐ-con-env = G.con-env tt
ISWIMᵐ-con = G.con tt
