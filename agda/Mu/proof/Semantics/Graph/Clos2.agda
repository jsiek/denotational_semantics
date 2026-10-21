{-

  Lemmas about the semantics of Clos2μ in the graph model
  (Mu/Semantics/Graph/Clos2.agda): the environment of the code of a
  closure (fv-env-pos).

-}

module Mu.proof.Semantics.Graph.Clos2 where

open import Mu.Semantics.Graph.Clos2 public

open import proof.Framework.GraphModel.DOpSig
open import proof.Framework.GraphModel.OpsBase using (nthD)
open import Mu.Language.Type using (Ctx; _∋_; Z; S; idx)
open import Mu.Framework.AllUtil using (pos)

open import Data.List using (length)
open import Data.Product using () renaming (_,_ to ⟨_,_⟩)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

fv-env-pos : ∀ {Δ : Ctx} {C} Xs (i : Δ ∋ C) → fv-env (length Δ) Xs (idx i) ≡ nthD Xs (pos i)
fv-env-pos ⟨ X , Xs ⟩ Z = refl
fv-env-pos ⟨ X , Xs ⟩ (S i) = fv-env-pos Xs i
