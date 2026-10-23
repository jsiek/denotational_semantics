{-

  Correctness of concretize (Closμ → EnvClosμ) in Scott domains
  (Mu/Semantics/ScottDomains/{Clos,EnvClos}.agda), as in the graph model
  (Mu/proof/Correctness/GraphModel/ConcretizeCorrect.agda), with equality of
  values in place of equality of sets, and without consistency.

  ⟦ M ⟧ ρ₂ = ⟦ concretize φ M ⟧₃ ρ₃ when each variable x of M means in
  ρ₂ what its reference φ x (a variable, or a component of a tuple)
  means in ρ₃ (EnvRel). Every case but the closure is a congruence. A
  Closμ closure is guarded by its free variables, and a EnvClosμ closure
  is its code, a function value, applied to their tuple T: it is
  seq T (the function of the code's body on T) (app-Λ), and a guard on
  the free variables is a seq on their tuple (guard-seq,
  Mu/proof/Semantics/ScottDomains/OptimizeLemmas.agda). When the free
  variables are defined, the code finds free variable i as get i of T
  (proj-tuple).

-}

open import MLTT.Spartan hiding (inl; inr; cases)
open import UF.FunExt
open import UF.PropTrunc
open import UF.Subsingletons
open import UF.Base using (ap₂; happly)

open import Mu.Language.Type
open import Mu.Language.Clos
import Mu.Language.EnvClos as T
open import Mu.Framework.AllUtil using (All; []; _∷_; pos)
open import Mu.Compiler.Concretize
open import Framework.abt.GSubst using (_•_)
open import Data.List using (List; []; _∷_; length)
open import Data.Fin using (Fin; zero; suc)

module Mu.proof.Correctness.ScottDomains.ConcretizeCorrect
        (pt : propositional-truncations-exist)
        (fe : Fun-Ext)
        (pe : propext 𝓤₀)
       where

open import Framework.Scott.Base pt fe
open import proof.Framework.Scott.Ops pt fe pe renaming (app to appᵈ; inl to inlᵈ; inr to inrᵈ; tuple to tupleᵈ)
open import proof.Framework.Scott.Semantics pt fe pe
open import Semantics.Scott.Prim pt fe pe using (primD)
open import Mu.Semantics.ScottDomains.Clos pt fe pe
open import Mu.Semantics.ScottDomains.EnvClos pt fe pe renaming (⟦_⟧ to ⟦_⟧₃; ⟦_⟧s to ⟦_⟧s₃)
open import Mu.proof.Semantics.ScottDomains.OptimizeLemmas pt fe pe using (guard-seq)

{- each variable means what its reference means -}
EnvRel : ∀ {Γ Γ'} → Refs Γ Γ' → ⟨ Env ⟩ → ⟨ Env ⟩ → 𝓤₁ ̇
EnvRel φ ρ₂ ρ₃ = ∀ {C} (x : _ ∋ C) → ρ₂ (idx x) ＝ ⟦ ref-tm (φ x) ⟧₃ · ρ₃

shift-ok : ∀ {Γ A B} (r : Ref Γ A) (X : ⟨ 𝔻 ⟩) (ρ : ⟨ Env ⟩) → ⟦ ref-tm (shift-ref {B = B} r) ⟧₃ · (X • ρ) ＝ ⟦ ref-tm r ⟧₃ · ρ
shift-ok (var x) X ρ = refl
shift-ok (prj i x) X ρ = refl

rel-ext : ∀ {Γ Γ' B} (φ : Refs Γ Γ') {ρ₂ ρ₃ : ⟨ Env ⟩} {X : ⟨ 𝔻 ⟩} → EnvRel φ ρ₂ ρ₃ → EnvRel (ext-ref {B = B} φ) (X • ρ₂) (X • ρ₃)
rel-ext φ rel Z = refl
rel-ext φ {ρ₃ = ρ₃} {X} rel (S x) = rel x ∙ (shift-ok (φ x) X ρ₃ ⁻¹)

{- free variable i in the environment of a closure's code -}
fv-pos : ∀ {Δ : Ctx} {C} (ds : Fin (length Δ) → ⟨ 𝔻 ⟩) (Y : ⟨ 𝔻 ⟩) (i : Δ ∋ C) → fv-env (length Δ) ds Y (succ (idx i)) ＝ ds (pos i)
fv-pos ds Y Z = refl
fv-pos ds Y (S i) = fv-pos (λ j → ds (suc j)) (ds zero) i

conc : ∀ {Γ Γ' A} (M : Tm Γ A) (φ : Refs Γ Γ') {ρ₂ ρ₃ : ⟨ Env ⟩} → EnvRel φ ρ₂ ρ₃ → ⟦ M ⟧ · ρ₂ ＝ ⟦ concretize φ M ⟧₃ · ρ₃
concs-ok : ∀ {Γ Γ' Δ} (Ms : All (Tm Γ) Δ) (φ : Refs Γ Γ') {ρ₂ ρ₃ : ⟨ Env ⟩} → EnvRel φ ρ₂ ρ₃
  → ⟦ Ms ⟧s · ρ₂ ＝ ⟦ concs φ Ms ⟧s₃ · ρ₃

{- a body under a binder -}
under : ∀ {Γ Γ' A B} (N : Tm (B ∷ Γ) A) (φ : Refs Γ Γ') {ρ₂ ρ₃ : ⟨ Env ⟩} → EnvRel φ ρ₂ ρ₃
  → (d : ⟨ 𝔻 ⟩) → defined d → ⟦ N ⟧ · (d • ρ₂) ＝ ⟦ concretize (ext-ref φ) N ⟧₃ · (d • ρ₃)
under N φ rel d _ = conc N (ext-ref φ) (rel-ext φ rel)

conc (` x) φ rel = rel x
conc (clos {Δ} N Ms) φ {ρ₂} {ρ₃} rel =
  guard-seq n xs (Λ · closure-fun n ⟦ N ⟧ xs) e'
    (λ ne → Λ-cong (closure-fun n ⟦ N ⟧ xs) (curry₁ 𝔻 𝔻 𝔻 B · t) λ Y _ →
      conc N fv-ref λ { Z → refl
                      ; (S i) → fv-pos xs Y i ∙ happly eqs (pos i)
                                ∙ (proj-tuple n ys (λ j → transport defined (happly eqs j) (ne j)) (pos i) ⁻¹) })
  ∙ ap (λ z → seq · (tupleᵈ n · z) · e') eqs
  ∙ (app-Λ G t ⁻¹)
  where
  n = length Δ
  xs = ⟦ Ms ⟧s · ρ₂
  ys = ⟦ concs φ Ms ⟧s₃ · ρ₃
  eqs = concs-ok Ms φ rel
  t = tupleᵈ n · ys
  B = ∘₁ (𝔻 ×₁ 𝔻) Env 𝔻 env₂ᶜ ⟦ concretize fv-ref N ⟧₃
  G = ∘₁ 𝔻 (𝔻 ⟹₁ 𝔻) 𝔻 (curry₁ 𝔻 𝔻 𝔻 B) Λ
  e' = Λ · (curry₁ 𝔻 𝔻 𝔻 B · t)
conc (app L M) φ rel = ap₂ (λ a b → appᵈ · a · b) (conc L φ rel) (conc M φ rel)
conc (lit B k) φ rel = refl
conc (tuple {Δ} Ms) φ rel = ap (tupleᵈ (length Δ) ·_) (concs-ok Ms φ rel)
conc (get i M) φ rel = ap (proj (pos i) ·_) (conc M φ rel)
conc (inl M) φ rel = ap (inlᵈ ·_) (conc M φ rel)
conc (inr M) φ rel = ap (inrᵈ ·_) (conc M φ rel)
conc (case L M N) φ {ρ₂} {ρ₃} rel =
  caseᶜ-cong ⟦ L ⟧ ⟦ concretize φ L ⟧₃ ⟦ M ⟧ ⟦ concretize (ext-ref φ) M ⟧₃ ⟦ N ⟧ ⟦ concretize (ext-ref φ) N ⟧₃ ρ₂ ρ₃
    (conc L φ rel) (under M φ rel) (under N φ rel)
conc (prim p L M) φ rel = ap₂ (λ a b → primD p · a · b) (conc L φ rel) (conc M φ rel)
conc (let′ M N) φ {ρ₂} {ρ₃} rel =
  letᶜ-cong ⟦ M ⟧ ⟦ concretize φ M ⟧₃ ⟦ N ⟧ ⟦ concretize (ext-ref φ) N ⟧₃ ρ₂ ρ₃ (conc M φ rel) (under N φ rel)
conc (fold M) φ rel = conc M φ rel
conc (unfold M) φ rel = conc M φ rel

concs-ok [] φ rel = refl
concs-ok (M ∷ Ms) φ rel = dfunext fe λ { zero → conc M φ rel ; (suc i) → happly (concs-ok Ms φ rel) i }

concretize-correct : ∀ {A} (M : Tm [] A) → ⟦ M ⟧ · ρ₀ ＝ ⟦ concretize-program M ⟧₃ · ρ₀
concretize-correct M = conc M (λ ()) (λ ())


