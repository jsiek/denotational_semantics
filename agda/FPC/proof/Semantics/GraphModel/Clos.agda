{-

  Lemmas about the semantics of Closμ in the graph model
  (Mu/Semantics/GraphModel/Clos.agda): the environment of the code of a
  closure (fv-env-pos).

-}

module Mu.proof.Semantics.GraphModel.Clos where

open import Mu.Semantics.GraphModel.Clos public

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
