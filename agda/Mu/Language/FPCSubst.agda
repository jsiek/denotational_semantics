{-

  Renaming and substitution of FPC (Mu/Language/FPC.agda): the traversal
  with a kit, one clause per constructor, and from it renaming (ren),
  substitution (sub) and the closing substitutions of a reduction
  semantics (_•_, ∅, _[_]), by the substitution of intrinsically typed
  terms (Framework/Syntax/TypedSubst.agda), as for Clos4ᵀ
  (Semantics/Reduction/Typed/Clos4.agda). The simplify pass
  (Mu/Compiler/Simplify.agda) renames, and the reduction semantics
  (Mu/Semantics/ReductionSemantics/FPC.agda) substitutes.

-}

module Mu.Language.FPCSubst where

open import Mu.Language.FPC
open import Mu.Framework.AllUtil using (All; []; _∷_)

open import Framework.Syntax.TypedSubst Tm `_ public

module _ (𝒦 : Kit) where
  open Kit 𝒦

  trav : ∀ {Γ Δ A} → Sub 𝒦 Γ Δ → Tm Γ A → Tm Δ A
  travs : ∀ {Γ Δ Δ'} → Sub 𝒦 Γ Δ → All (Tm Γ) Δ' → All (Tm Δ) Δ'
  trav σ (` x) = tm (σ x)
  trav σ (lam N) = lam (trav (exts 𝒦 σ) N)
  trav σ (app L M) = app (trav σ L) (trav σ M)
  trav σ (lit B c) = lit B c
  trav σ (tuple Ms) = tuple (travs σ Ms)
  trav σ (get i M) = get i (trav σ M)
  trav σ (inl M) = inl (trav σ M)
  trav σ (inr M) = inr (trav σ M)
  trav σ (case L M N) = case (trav σ L) (trav (exts 𝒦 σ) M) (trav (exts 𝒦 σ) N)
  trav σ (prim p L M) = prim p (trav σ L) (trav σ M)
  trav σ (let′ M N) = let′ (trav σ M) (trav (exts 𝒦 σ) N)
  trav σ (fold M) = fold (trav σ M)
  trav σ (unfold M) = unfold (trav σ M)
  travs σ [] = []
  travs σ (M ∷ Ms) = trav σ M ∷ travs σ Ms

open Substitution trav public
