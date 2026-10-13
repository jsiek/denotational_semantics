{-

  The graph-model operators that the graph model (Ops.agda) and the graph
  model with errors (ErrorOps.agda) share unchanged: constants, and the
  components of a tuple of results.

-}

module Framework.GraphModel.OpsBase where

open import Framework.Primitives
open import Framework.GraphModel.SetsAsPredicates
open import Framework.abt.Sig using (Sig; ν; ■; Result)
open import Framework.GraphModel.DOpSig
open import Framework.GraphModel.Domain

open import Data.Empty renaming (⊥ to False)
open import Data.List using (List ; _∷_ ; []; replicate)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Fin using (Fin; zero; suc)
open import Data.Product using (Σ-syntax) renaming (_,_ to ⟨_,_⟩)
open import Relation.Binary.PropositionalEquality using (_≡_; subst)

{- a constant -}
ℬ : (B : Base) → base-rep B → DOp (𝒫 Value) []
ℬ B k _ (const {B′} k′) = Σ[ B≡ ∈ B ≡ B′ ] (subst base-rep B≡ k) ≡ k′
ℬ B k _ _ = False

{- component i of a tuple of n results -}
nthD : ∀ {n}{ℓ}{A : Set ℓ} → Results A (replicate n ■) → (i : Fin n) → Result A ■
nthD {.(suc _)} ⟨ D , Ds ⟩ zero = D
nthD {.(suc _)} ⟨ D , Ds ⟩ (suc i) = nthD Ds i
