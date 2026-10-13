module proof.Semantics.Graph.ISWIM where

open import proof.Framework.GraphModel.DOpSig
open import proof.Framework.GraphModel.SetsAsPredicates
open import proof.Framework.GraphModel.DenotProperties
open import proof.Framework.GraphModel.Domain
open import proof.Framework.GraphModel.Ops
open import proof.Semantics.Graph.Prim
open import Language.ISWIM
open import Semantics.Graph.ISWIM public hiding (⟦_⟧; init)

open import Level renaming (zero to lzero; suc to lsuc)
open import proof.Framework.GraphModel.Env using (_~ₑ[_]_)

{- The semantics of Semantics/Graph/ISWIM.agda as an instance of
   the generic Semantics record (proof/Framework/GraphModel/Semantics.agda),
   whose ⟦_⟧ is by definition the ⟦_⟧ there, with the monotonicity and
   consistency of its operators. -}

𝕆-ISWIM-mono : 𝕆-monotone sig 𝕆-ISWIM
𝕆-ISWIM-mono lam = Λ-mono
𝕆-ISWIM-mono app = ⋆-mono
𝕆-ISWIM-mono (lit B k) _ _ _ = lift (λ d z → z)
𝕆-ISWIM-mono (tuple x) = 𝒯-mono x
𝕆-ISWIM-mono (get x) = proj-mono x
𝕆-ISWIM-mono inl-op = inl-mono
𝕆-ISWIM-mono inr-op = inr-mono
𝕆-ISWIM-mono case-op = 𝒞-mono
𝕆-ISWIM-mono (prim p) = primD-mono p

𝕆-ISWIM-consis : 𝕆-consistent _~_ sig 𝕆-ISWIM
𝕆-ISWIM-consis lam = Λ-consis
𝕆-ISWIM-consis app = ⋆-consis
𝕆-ISWIM-consis (lit B k) = ℬ-consis B k
𝕆-ISWIM-consis (tuple x) = 𝒯-consis x
𝕆-ISWIM-consis (get x) = proj-consis x
𝕆-ISWIM-consis inl-op = inl-consis
𝕆-ISWIM-consis inr-op = inr-consis
𝕆-ISWIM-consis case-op = 𝒞-consis
𝕆-ISWIM-consis (prim p) = primD-consis p

open import proof.Framework.GraphModel.Semantics Op sig public

instance
  ISWIM-Semantics : Semantics
  ISWIM-Semantics = record { interp-op = 𝕆-ISWIM ;
                             mono-op = 𝕆-ISWIM-mono ;
                             error = ω }
open Semantics {{...}} public

{- consistent environments give consistent denotations -}
ISWIM-con-env : ∀ M {ρ ρ'} → ρ ~ₑ[ Every _~_ ] ρ' → Every _~_ (⟦ M ⟧ ρ) (⟦ M ⟧ ρ')
ISWIM-con-env M = ⟦⟧-pres (Every _~_) 𝕆-ISWIM-consis (Con-⌈⌉ ω) M
