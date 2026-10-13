module proof.Semantics.GraphErr.ISWIM where

open import proof.Framework.GraphModel.ContinuityBase using (Good; ℬ-good)
open import proof.Framework.GraphModel.ErrorContinuity
open import proof.Semantics.GraphErr.Prim
open import Language.ISWIM
open import Semantics.GraphErr.ISWIM public hiding (⟦_⟧; init)
open import proof.Framework.GraphModel.SemanticsCore Op sig using (module GoodSemantics)

open import Data.Unit using (⊤; tt)

{- The semantics of Semantics/GraphErr/ISWIM.agda as an instance of the
   generic Semantics record (proof/Framework/GraphModel/Semantics.agda),
   whose ⟦_⟧ is by definition the ⟦_⟧ there: its operators are Good
   (monotone, consistent and continuous). -}

private
  good : ∀ op → Good ⊤ (sig op) (𝕆-ISWIMᵉ op)
  good lam = Λᵉ-good
  good app = ⋆ᵉ-good
  good (lit B k) = ℬ-good B k
  good (tuple n) = 𝒯ᵉ-good n
  good (get i) = projᵉ-good i
  good inl-op = inlᵉ-good
  good inr-op = inrᵉ-good
  good case-op = 𝒞ᵉ-good
  good (prim p) = primᵉ-good p
  good let-op = letᵉ-good

  module G = GoodSemantics ⊤ 𝕆-ISWIMᵉ good

open import proof.Framework.GraphModel.Semantics Op sig public

instance
  ISWIMᵉ-Semantics : Semantics
  ISWIMᵉ-Semantics = G.Sem
open Semantics {{...}} public

ISWIMᵉ-Continuous : ContinuousSemantics
ISWIMᵉ-Continuous = G.Cont-Sem

open G public using (term-continuous; body-mono; body-continuous)

{- consistent environments give consistent denotations -}
ISWIMᵉ-con-env = G.con-env tt
ISWIMᵉ-con = G.con tt
