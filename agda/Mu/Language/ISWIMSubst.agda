{-

  Renaming and substitution of ISWIMμ (Mu/Language/ISWIM.agda): one
  traversal with a kit (Framework/Syntax/Kit.agda), over contexts that
  are lists of types, as for Clos4ᵀ (Semantics/Reduction/Typed/Clos4.agda).
  The simplify pass (Mu/Compiler/Simplify.agda) renames, and the
  reduction semantics (Mu/Semantics/ReductionSemantics/ISWIM.agda) substitutes.

-}

module Mu.Language.ISWIMSubst where

open import Mu.Language.Type
open import Mu.Language.ISWIM
open import Mu.Framework.AllUtil using (All; []; _∷_)

open import Data.List using (_∷_)

open import Framework.Syntax.Kit {Ctx} {Type} _∋_ (λ Γ A → A ∷ Γ) Tm public

module _ (𝒦 : Kit) where
  open Kit 𝒦

  exts : ∀ {Γ Δ B} → Sub 𝒦 Γ Δ → Sub 𝒦 (B ∷ Γ) (B ∷ Δ)
  exts σ Z = vr Z
  exts σ (S x) = wk (σ x)

  trav : ∀ {Γ Δ A} → Sub 𝒦 Γ Δ → Tm Γ A → Tm Δ A
  travs : ∀ {Γ Δ Δ'} → Sub 𝒦 Γ Δ → All (Tm Γ) Δ' → All (Tm Δ) Δ'
  trav σ (` x) = tm (σ x)
  trav σ (lam N) = lam (trav (exts σ) N)
  trav σ (app L M) = app (trav σ L) (trav σ M)
  trav σ (lit B c) = lit B c
  trav σ (tuple Ms) = tuple (travs σ Ms)
  trav σ (get i M) = get i (trav σ M)
  trav σ (inl M) = inl (trav σ M)
  trav σ (inr M) = inr (trav σ M)
  trav σ (case L M N) = case (trav σ L) (trav (exts σ) M) (trav (exts σ) N)
  trav σ (prim p L M) = prim p (trav σ L) (trav σ M)
  trav σ (let′ M N) = let′ (trav σ M) (trav (exts σ) N)
  trav σ (fold M) = fold (trav σ M)
  trav σ (unfold M) = unfold (trav σ M)
  travs σ [] = []
  travs σ (M ∷ Ms) = trav σ M ∷ travs σ Ms

varK : Kit
varK = record { K = _∋_ ; vr = λ x → x ; tm = `_ ; wk = S }

ren : ∀ {Γ Δ A} → (∀ {B} → Γ ∋ B → Δ ∋ B) → Tm Γ A → Tm Δ A
ren r = trav varK r

tmK : Kit
tmK = record { K = Tm ; vr = `_ ; tm = λ M → M ; wk = ren S }

sub : ∀ {Γ Δ A} → (∀ {B} → Γ ∋ B → Tm Δ B) → Tm Γ A → Tm Δ A
sub σ = trav tmK σ
