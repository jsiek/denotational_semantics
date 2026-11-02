{-

  Correctness of concretize (Closμ → EnvClosμ) in the graph model
  (Mu/Semantics/GraphModel/{Clos,EnvClos}.agda), as for typed concretize
  (proof/Correctness/Graph/ConcretizeCorrect.agda).

  ⟦ M ⟧ ρ₂ ≃ ⟦ concretize φ M ⟧₃ ρ₃ when each variable x of M means in ρ₂
  what its reference φ x (a variable, or a component of a tuple) means
  in ρ₃ (EnvRel), for a consistent ρ₃. Every case but the closure is a
  congruence. A Closμ closure is strict in its free variables, and a
  EnvClosμ closure is its code applied to their tuple T, which is nonempty
  exactly when they are; then it is the function of the code's body on
  T (ΛΛ-⋆, by the continuity of EnvClosμ terms), and the code finds free
  variable i as get i of T (proj-𝒯).

-}

module Mu.proof.Correctness.GraphModel.ConcretizeCorrect where

open import proof.Framework.GraphModel.Prelude hiding (ρ₀)
open import Mu.Semantics.GraphModel.Closed using (ρ₀)
open import proof.Framework.GraphModel.Ops
open import proof.Framework.GraphModel.Env using (Env; •-~)
open import proof.Framework.GraphModel.TypedGraph using (ΛΛ-⋆; 𝒯-ne; 𝒯-intro; proj-𝒯)
open import proof.Framework.GraphModel.TypedOkBase using (fin-code)
open import proof.Semantics.Graph.Prim using (primD-≃)
open import Mu.Language.Type
open import Mu.Language.Clos
import Mu.Language.EnvClos as T
open import Mu.proof.Semantics.GraphModel.Clos using (⟦_⟧; ⟦_⟧s; fv-env; fv-env-pos)
open import Mu.proof.Semantics.GraphModel.EnvClos using (ok; con) renaming (⟦_⟧ to ⟦_⟧₃; ⟦_⟧s to ⟦_⟧s₃)
open import Mu.proof.Semantics.GraphModel.Binders using (lam-≃; let-≃; case-≃; ne-≃; guard-yes)
open import Mu.Framework.AllUtil using (All; []; _∷_; pos)
open import Mu.Compiler.Concretize

open import Data.Fin using (zero; suc)
open import Data.List using (List; []; _∷_; length)
open import Data.Product using (_×_; proj₁) renaming (_,_ to ⟨_,_⟩)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)

{- each variable means what its reference means -}
EnvRel : ∀ {Γ Γ'} → Refs Γ Γ' → Env Value → Env Value → Set
EnvRel φ ρ₂ ρ₃ = ∀ {C} (x : _ ∋ C) → ρ₂ (idx x) ≃ ⟦ ref-tm (φ x) ⟧₃ ρ₃

shift-ok : ∀ {Γ A B} (r : Ref Γ A) X ρ → ⟦ ref-tm (shift-ref {B = B} r) ⟧₃ (X • ρ) ≡ ⟦ ref-tm r ⟧₃ ρ
shift-ok (var x) X ρ = refl
shift-ok (prj i x) X ρ = refl

rel-ext : ∀ {Γ Γ' B} {φ : Refs Γ Γ'} {ρ₂ ρ₃} → EnvRel φ ρ₂ ρ₃ → ∀ {X} → EnvRel (ext-ref {B = B} φ) (X • ρ₂) (X • ρ₃)
rel-ext rel Z = ≃-refl
rel-ext {φ = φ} {ρ₃ = ρ₃} rel {X} (S x) = ≃-trans (rel x) (≃-reflexive (sym (shift-ok (φ x) X ρ₃)))

conc : ∀ {Γ Γ' A} (M : Tm Γ A) (φ : Refs Γ Γ') {ρ₂ ρ₃} → Con-env ρ₃ → EnvRel φ ρ₂ ρ₃
  → ⟦ M ⟧ ρ₂ ≃ ⟦ concretize φ M ⟧₃ ρ₃
concs-nth : ∀ {Γ Γ' Δ} (Ms : All (Tm Γ) Δ) (φ : Refs Γ Γ') {ρ₂ ρ₃} → Con-env ρ₃ → EnvRel φ ρ₂ ρ₃
  → ∀ i → nthD (⟦ Ms ⟧s ρ₂) i ≃ nthD (⟦ concs φ Ms ⟧s₃ ρ₃) i

conc (` x) φ c rel = rel x
conc (clos {Δ} N Ms) φ {ρ₂} {ρ₃} c rel =
  ≃-when (λ { w ⟨ ne , _ ⟩ i → ne-≃ (concs-nth Ms φ c rel i) (ne i) })
    (λ { w ⟨ V , ⟨ _ , ⟨ V⊆ , neV ⟩ ⟩ ⟩ → 𝒯-ne n (ne-mem neV V⊆) }) λ ne →
  ≃-trans (guard-yes λ i → ne-≃ (≃-sym (concs-nth Ms φ c rel i)) (ne i))
    (≃-trans (lam-≃ λ X _ cX → conc N fv-ref (Con-• cX (Con-• cT (λ _ → Con-⌈⌉ ⟨⟩)))
                λ { Z → ≃-refl
                  ; (S i) → ≃-trans (≃-reflexive (fv-env-pos Ds i))
                              (≃-trans (concs-nth Ms φ c rel (pos i)) (≃-sym (proj-𝒯 n ne (pos i)))) })
      (≃-sym (ΛΛ-⋆ cT (𝒯-intro n ne)
        (λ X⊆ → proj₁ (ok N') (•-~ _⊆_ (•-~ _⊆_ (λ _ _ z → z) X⊆) (λ _ z → z))) (fin-code (ok N') (𝒯-intro n ne)))))
  where
  n = length Δ
  N' = concretize fv-ref N
  Ds = ⟦ Ms ⟧s ρ₂
  cT = con (T.tuple (concs φ Ms)) c
conc (app L M) φ c rel = ⋆-≃ (conc L φ c rel) (conc M φ c rel)
conc (lit B k) φ c rel = ≃-refl
conc (tuple {Δ} Ms) φ c rel = 𝒯-≃ (length Δ) (concs-nth Ms φ c rel)
conc (get i M) φ c rel = proj-≃ (pos i) (conc M φ c rel)
conc (inl M) φ c rel = inl-≃ (conc M φ c rel)
conc (inr M) φ c rel = inr-≃ (conc M φ c rel)
conc (case L M N) φ {ρ₂} {ρ₃} c rel =
  case-≃ (conc L φ c rel) (λ X _ cX → conc M (ext-ref φ) {X • ρ₂} (Con-• cX c) (rel-ext rel))
    (λ X _ cX → conc N (ext-ref φ) {X • ρ₂} (Con-• cX c) (rel-ext rel))
conc (prim p L M) φ c rel = primD-≃ p (conc L φ c rel) (conc M φ c rel)
conc (let′ M N) φ {ρ₂} c rel = let-≃ (conc M φ c rel) λ X _ cX → conc N (ext-ref φ) {X • ρ₂} (Con-• cX c) (rel-ext rel)
conc (fold M) φ c rel = conc M φ c rel
conc (unfold M) φ c rel = conc M φ c rel

concs-nth (M ∷ Ms) φ c rel zero = conc M φ c rel
concs-nth (M ∷ Ms) φ c rel (suc i) = concs-nth Ms φ c rel i

concretize-correct : ∀ {A} (M : Tm [] A) → ⟦ M ⟧ ρ₀ ≃ ⟦ concretize-program M ⟧₃ ρ₀
concretize-correct M = conc M (λ ()) (λ _ → Con-⌈⌉ ⟨⟩) (λ ())
