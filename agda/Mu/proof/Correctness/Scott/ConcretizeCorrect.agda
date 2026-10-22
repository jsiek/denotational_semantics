{-

  Correctness of concretize (Clos2μ → Clos3μ) in Scott domains
  (Mu/Semantics/Scott/{Clos2,Clos3}.agda), as in the graph model
  (Mu/proof/Correctness/Graph/ConcretizeCorrect.agda), with equality of
  values in place of equality of sets, and without consistency.

  ⟦ M ⟧ ρ₂ = ⟦ concretize φ M ⟧₃ ρ₃ when each variable x of M means in
  ρ₂ what its reference φ x (a variable, or a component of a tuple)
  means in ρ₃ (EnvRel). Every case but the closure is a congruence. A
  Clos2μ closure is guarded by its free variables, and a Clos3μ closure
  is its code, a function value, applied to their tuple T: it is
  seq T (the function of the code's body on T) (app-Λ), and a guard on
  the free variables is a seq on their tuple (guard-seq,
  Mu/proof/Semantics/Scott/OptimizeLemmas.agda). When the free
  variables are defined, the code finds free variable i as get i of T
  (proj-tuple).

-}

open import MLTT.Spartan hiding (inl; inr; cases)
open import UF.FunExt
open import UF.PropTrunc
open import UF.Subsingletons
open import UF.Base using (ap₂; happly)

open import Mu.Language.Type
open import Mu.Language.Clos2
import Mu.Language.Clos3 as T
open import Mu.Framework.AllUtil using (All; []; _∷_; pos)
open import Mu.Compiler.Concretize
open import Framework.abt.GSubst using (_•_)
open import Data.List using (List; []; _∷_; length)
open import Data.Fin using (Fin; zero; suc)

module Mu.proof.Correctness.Scott.ConcretizeCorrect
        (pt : propositional-truncations-exist)
        (fe : Fun-Ext)
        (pe : propext 𝓤₀)
       where

open import Framework.Scott.Base pt fe
open import proof.Framework.Scott.Ops pt fe pe renaming (app to appᵈ; inl to inlᵈ; inr to inrᵈ; tuple to tupleᵈ)
open import proof.Framework.Scott.Semantics pt fe pe
open import Semantics.Scott.Prim pt fe pe using (primD)
open import Mu.Semantics.Scott.Clos2 pt fe pe
open import Mu.Semantics.Scott.Clos3 pt fe pe renaming (⟦_⟧ to ⟦_⟧₃; ⟦_⟧s to ⟦_⟧s₃)
open import Mu.proof.Semantics.Scott.OptimizeLemmas pt fe pe using (guard-seq)

{- each variable means what its reference means -}
EnvRel : ∀ {Γ Γ'} → Refs Γ Γ' → ⟨ Env ⟩ → ⟨ Env ⟩ → 𝓤₁ ̇
EnvRel φ ρ₂ ρ₃ = ∀ {C} (x : _ ∋ C) → ρ₂ (idx x) ＝ ⟦ ref-tm (φ x) ⟧₃ · ρ₃

shift-ok : ∀ {Γ A B} (r : Ref Γ A) (X : ⟨ 𝔻 ⟩) (ρ : ⟨ Env ⟩) → ⟦ ref-tm (shift-ref {B = B} r) ⟧₃ · (X • ρ) ＝ ⟦ ref-tm r ⟧₃ · ρ
shift-ok (var x) X ρ = refl
shift-ok (prj i x) X ρ = refl

rel-ext : ∀ {Γ Γ' B} (φ : Refs Γ Γ') (ρ₂ ρ₃ : ⟨ Env ⟩) → EnvRel φ ρ₂ ρ₃ → (X : ⟨ 𝔻 ⟩) → EnvRel (ext-ref {B = B} φ) (X • ρ₂) (X • ρ₃)
rel-ext φ ρ₂ ρ₃ rel X Z = refl
rel-ext φ ρ₂ ρ₃ rel X (S x) = rel x ∙ (shift-ok (φ x) X ρ₃ ⁻¹)

{- free variable i in the environment of a closure's code -}
fv-pos : ∀ {Δ : Ctx} {C} (ds : Fin (length Δ) → ⟨ 𝔻 ⟩) (Y : ⟨ 𝔻 ⟩) (i : Δ ∋ C) → fv-env (length Δ) ds Y (succ (idx i)) ＝ ds (pos i)
fv-pos ds Y Z = refl
fv-pos ds Y (S i) = fv-pos (λ j → ds (suc j)) (ds zero) i

conc : ∀ {Γ Γ' A} (M : Tm Γ A) (φ : Refs Γ Γ') (ρ₂ ρ₃ : ⟨ Env ⟩) → EnvRel φ ρ₂ ρ₃
  → ⟦ M ⟧ · ρ₂ ＝ ⟦ concretize φ M ⟧₃ · ρ₃
concs-ok : ∀ {Γ Γ' Δ} (Ms : All (Tm Γ) Δ) (φ : Refs Γ Γ') (ρ₂ ρ₃ : ⟨ Env ⟩) → EnvRel φ ρ₂ ρ₃
  → ⟦ Ms ⟧s · ρ₂ ＝ ⟦ concs φ Ms ⟧s₃ · ρ₃

{- a body under a binder -}
under : ∀ {Γ Γ' A B} (N : Tm (B ∷ Γ) A) (φ : Refs Γ Γ') (ρ₂ ρ₃ : ⟨ Env ⟩) → EnvRel φ ρ₂ ρ₃
  → (d : ⟨ 𝔻 ⟩) → defined d → ⟦ N ⟧ · (d • ρ₂) ＝ ⟦ concretize (ext-ref φ) N ⟧₃ · (d • ρ₃)
under N φ ρ₂ ρ₃ rel d _ = conc N (ext-ref φ) (d • ρ₂) (d • ρ₃) (rel-ext φ ρ₂ ρ₃ rel d)

conc (` x) φ ρ₂ ρ₃ rel = rel x
conc (clos {Δ} N Ms) φ ρ₂ ρ₃ rel =
  guard-seq n xs (Λ · closure-fun n ⟦ N ⟧ xs) e'
    (λ ne → Λ-cong (closure-fun n ⟦ N ⟧ xs) (curry₁ 𝔻 𝔻 𝔻 B · t) λ Y _ →
      conc N fv-ref (fv-env n xs Y) (env₂ t Y)
        λ { Z → refl
          ; (S i) → fv-pos xs Y i ∙ happly eqs (pos i)
                    ∙ (proj-tuple n ys (λ j → transport defined (happly eqs j) (ne j)) (pos i) ⁻¹) })
  ∙ ap (λ z → seq · (tupleᵈ n · z) · e') eqs
  ∙ (app-Λ G t ⁻¹)
  where
  n = length Δ
  xs = ⟦ Ms ⟧s · ρ₂
  ys = ⟦ concs φ Ms ⟧s₃ · ρ₃
  eqs = concs-ok Ms φ ρ₂ ρ₃ rel
  t = tupleᵈ n · ys
  B : DCPO[ 𝔻 ×₁ 𝔻 , 𝔻 ]
  B = ∘₁ (𝔻 ×₁ 𝔻) Env 𝔻 env₂ᶜ ⟦ concretize fv-ref N ⟧₃
  G : DCPO[ 𝔻 , 𝔻 ]
  G = ∘₁ 𝔻 (𝔻 ⟹₁ 𝔻) 𝔻 (curry₁ 𝔻 𝔻 𝔻 B) Λ
  e' = Λ · (curry₁ 𝔻 𝔻 𝔻 B · t)
conc (app L M) φ ρ₂ ρ₃ rel = ap₂ (λ a b → appᵈ · a · b) (conc L φ ρ₂ ρ₃ rel) (conc M φ ρ₂ ρ₃ rel)
conc (lit B k) φ ρ₂ ρ₃ rel = refl
conc (tuple {Δ} Ms) φ ρ₂ ρ₃ rel = ap (tupleᵈ (length Δ) ·_) (concs-ok Ms φ ρ₂ ρ₃ rel)
conc (get i M) φ ρ₂ ρ₃ rel = ap (proj (pos i) ·_) (conc M φ ρ₂ ρ₃ rel)
conc (inl M) φ ρ₂ ρ₃ rel = ap (inlᵈ ·_) (conc M φ ρ₂ ρ₃ rel)
conc (inr M) φ ρ₂ ρ₃ rel = ap (inrᵈ ·_) (conc M φ ρ₂ ρ₃ rel)
conc (case L M N) φ ρ₂ ρ₃ rel =
  caseᶜ-cong ⟦ L ⟧ ⟦ concretize φ L ⟧₃ ⟦ M ⟧ ⟦ concretize (ext-ref φ) M ⟧₃ ⟦ N ⟧ ⟦ concretize (ext-ref φ) N ⟧₃ ρ₂ ρ₃
    (conc L φ ρ₂ ρ₃ rel) (under M φ ρ₂ ρ₃ rel) (under N φ ρ₂ ρ₃ rel)
conc (prim p L M) φ ρ₂ ρ₃ rel = ap₂ (λ a b → primD p · a · b) (conc L φ ρ₂ ρ₃ rel) (conc M φ ρ₂ ρ₃ rel)
conc (let′ M N) φ ρ₂ ρ₃ rel =
  letᶜ-cong ⟦ M ⟧ ⟦ concretize φ M ⟧₃ ⟦ N ⟧ ⟦ concretize (ext-ref φ) N ⟧₃ ρ₂ ρ₃ (conc M φ ρ₂ ρ₃ rel) (under N φ ρ₂ ρ₃ rel)
conc (fold M) φ ρ₂ ρ₃ rel = conc M φ ρ₂ ρ₃ rel
conc (unfold M) φ ρ₂ ρ₃ rel = conc M φ ρ₂ ρ₃ rel

concs-ok [] φ ρ₂ ρ₃ rel = refl
concs-ok (M ∷ Ms) φ ρ₂ ρ₃ rel = dfunext fe λ { zero → conc M φ ρ₂ ρ₃ rel ; (suc i) → happly (concs-ok Ms φ ρ₂ ρ₃ rel) i }

concretize-correct : ∀ {A} (M : Tm [] A) → ⟦ M ⟧ · ρ₀ ＝ ⟦ concretize-program M ⟧₃ · ρ₀
concretize-correct M = conc M (λ ()) ρ₀ ρ₀ (λ ())
