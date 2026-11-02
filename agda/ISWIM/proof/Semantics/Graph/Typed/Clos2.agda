{-

  Lemmas about the semantics of Clos2ᵀ in the graph model
  (Semantics/Graph/Typed/Clos2.agda): the environment of the code of a
  closure (fv-env-nth).

-}

module proof.Semantics.Graph.Typed.Clos2 where

open import Semantics.Graph.Typed.Clos2 public

open import proof.Framework.GraphModel.DOpSig
open import proof.Framework.GraphModel.OpsBase using (nthD)

open import Data.Fin using (Fin; zero; suc; toℕ)
open import Data.Nat using (suc)
open import Data.Product using () renaming (_,_ to ⟨_,_⟩)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

fv-env-nth : ∀ n Xs (i : Fin n) → fv-env n Xs (toℕ i) ≡ nthD Xs i
fv-env-nth (suc n) ⟨ X , Xs ⟩ zero = refl
fv-env-nth (suc n) ⟨ X , Xs ⟩ (suc i) = fv-env-nth n Xs i
