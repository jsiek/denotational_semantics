{-

  Correctness of capture (ISWIMμ → Closμ) in Scott domains
  (Mu/Semantics/ScottDomains/{ISWIM,Clos}.agda), as in the graph model
  (Mu/proof/Correctness/GraphModel/CaptureCorrect.agda), with equality of
  values in place of equality of sets.

  ⟦ M ⟧ ρ = ⟦ capture M ⟧₂ ρ' when the environments agree on the
  variables in scope and ρ' is defined there (Rel). Every case but the
  function is a congruence (fold and unfold are the identity). A
  function becomes a closure that captures all variables of its
  context: they are defined, so its guard holds, and the code's
  environment fv-env agrees with ρ' on them. Bodies under binders need
  agree only on defined values, as function values and the branches of
  a case are strict.

-}

open import MLTT.Spartan hiding (inl; inr; cases)
open import UF.FunExt
open import UF.PropTrunc
open import UF.Subsingletons
open import UF.Base using (ap₂; happly)

open import Mu.Language.Type
open import Mu.Language.ISWIM
import Mu.Language.Clos as T
open import Mu.Framework.AllUtil using (All; []; _∷_; tab; pos)
open import Mu.Compiler.Capture
open import Framework.abt.GSubst using (_•_)
open import Data.List using (List; []; _∷_; length)
open import Data.Fin using (Fin; zero; suc)

module Mu.proof.Correctness.ScottDomains.CaptureCorrect
        (pt : propositional-truncations-exist)
        (fe : Fun-Ext)
        (pe : propext 𝓤₀)
       where

open import Framework.Scott.Base pt fe
open import proof.Framework.Scott.Ops pt fe pe renaming (app to appᵈ; inl to inlᵈ; inr to inrᵈ; tuple to tupleᵈ)
open import proof.Framework.Scott.Semantics pt fe pe
open import Semantics.Scott.Prim pt fe pe using (primD)
open import Mu.Semantics.ScottDomains.ISWIM pt fe pe
open import Mu.Semantics.ScottDomains.Clos pt fe pe renaming (⟦_⟧ to ⟦_⟧₂; ⟦_⟧s to ⟦_⟧s₂)

Rel : Ctx → ⟨ Env ⟩ → ⟨ Env ⟩ → 𝓤₁ ̇
Rel Γ ρ ρ' = ∀ {C} (x : Γ ∋ C) → (ρ (idx x) ＝ ρ' (idx x)) × defined (ρ' (idx x))

rel-ext : ∀ {Γ A ρ ρ'} (d : ⟨ 𝔻 ⟩) → defined d → Rel Γ ρ ρ' → Rel (A ∷ Γ) (d • ρ) (d • ρ')
rel-ext d p r Z = refl , p
rel-ext d p r (S x) = r x

{- the free variables of a closure built by tab -}
tab-fv : ∀ {Γ Δ C} (f : ∀ {A} → Δ ∋ A → T.Tm Γ A) (ρ : ⟨ Env ⟩) (Y : ⟨ 𝔻 ⟩) (x : Δ ∋ C)
  → fv-env (length Δ) (⟦ tab f ⟧s₂ · ρ) Y (succ (idx x)) ＝ ⟦ f x ⟧₂ · ρ
tab-fv f ρ Y Z = refl
tab-fv f ρ Y (S x) = tab-fv (λ y → f (S y)) ρ (⟦ f Z ⟧₂ · ρ) x

tab-defined : ∀ {Γ Δ} (f : ∀ {A} → Δ ∋ A → T.Tm Γ A) (ρ : ⟨ Env ⟩)
  → (∀ {A} (x : Δ ∋ A) → defined (⟦ f x ⟧₂ · ρ)) → (i : Fin (length Δ)) → defined ((⟦ tab f ⟧s₂ · ρ) i)
tab-defined {Δ = A ∷ Δ} f ρ h zero = h Z
tab-defined {Δ = A ∷ Δ} f ρ h (suc i) = tab-defined (λ y → f (S y)) ρ (λ x → h (S x)) i

enc : ∀ {Γ A} (M : Tm Γ A) {ρ ρ'} → Rel Γ ρ ρ' → ⟦ M ⟧ · ρ ＝ ⟦ capture M ⟧₂ · ρ'
encs-ok : ∀ {Γ Δ} (Ms : All (Tm Γ) Δ) {ρ ρ'} → Rel Γ ρ ρ' → ⟦ Ms ⟧s · ρ ＝ ⟦ encs Ms ⟧s₂ · ρ'

{- a body under a binder -}
under : ∀ {Γ A B} (N : Tm (A ∷ Γ) B) {ρ ρ'} → Rel Γ ρ ρ'
  → (d : ⟨ 𝔻 ⟩) → defined d → ⟦ N ⟧ · (d • ρ) ＝ ⟦ capture N ⟧₂ · (d • ρ')
under N r d p = enc N (rel-ext d p r)

enc (` x) r = pr₁ (r x)
enc {Γ} (lam N) {ρ} {ρ'} r =
  Λ-cong (abs ⟦ N ⟧ · ρ) (closure-fun (length Γ) ⟦ capture N ⟧₂ xs)
    (λ d p → enc N (λ { Z → refl , p
                      ; (S x) → (pr₁ (r x) ∙ (tab-fv T.`_ ρ' d x ⁻¹))
                              , transport defined (tab-fv T.`_ ρ' d x ⁻¹) (pr₂ (r x)) }))
  ∙ (guard-defined (length Γ) xs (tab-defined T.`_ ρ' (λ x → pr₂ (r x)))
       (Λ · closure-fun (length Γ) ⟦ capture N ⟧₂ xs) ⁻¹)
 where
  xs = ⟦ tab {P = T.Tm Γ} T.`_ ⟧s₂ · ρ'
enc (app L M) r = ap₂ (λ a b → appᵈ · a · b) (enc L r) (enc M r)
enc (lit B c) r = refl
enc (tuple {Δ} Ms) r = ap (tupleᵈ (length Δ) ·_) (encs-ok Ms r)
enc (get i M) r = ap (proj (pos i) ·_) (enc M r)
enc (inl M) r = ap (inlᵈ ·_) (enc M r)
enc (inr M) r = ap (inrᵈ ·_) (enc M r)
enc (case L M N) {ρ} {ρ'} r =
  caseᶜ-cong ⟦ L ⟧ ⟦ capture L ⟧₂ ⟦ M ⟧ ⟦ capture M ⟧₂ ⟦ N ⟧ ⟦ capture N ⟧₂ ρ ρ' (enc L r) (under M r) (under N r)
enc (prim p L M) r = ap₂ (λ a b → primD p · a · b) (enc L r) (enc M r)
enc (let′ M N) {ρ} {ρ'} r = letᶜ-cong ⟦ M ⟧ ⟦ capture M ⟧₂ ⟦ N ⟧ ⟦ capture N ⟧₂ ρ ρ' (enc M r) (under N r)
enc (fold M) r = enc M r
enc (unfold M) r = enc M r

encs-ok [] r = refl
encs-ok (M ∷ Ms) r = dfunext fe λ { zero → enc M r ; (suc i) → happly (encs-ok Ms r) i }

capture-correct : ∀ {A} (M : Tm [] A) → ⟦ M ⟧ · ρ₀ ＝ ⟦ capture M ⟧₂ · ρ₀
capture-correct M = enc M (λ ())
