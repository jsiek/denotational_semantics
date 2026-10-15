{-

  Correctness of concretize (Clos2μ → Clos3μ) in the graph model
  (Mu/Semantics/Graph/{Clos2,Clos3}.agda), as for typed concretize
  (proof/Correctness/Graph/ConcretizeCorrect.agda).

  ⟦ M ⟧ ρ₂ ≃ ⟦ concretize φ M ⟧₃ ρ₃ when each variable x of M means in ρ₂
  what its reference φ x (a variable, or a component of a tuple) means
  in ρ₃ (EnvRel), for a consistent ρ₃. Every case but the closure is a
  congruence. A Clos2μ closure is strict in its free variables, and a
  Clos3μ closure is its code applied to their tuple T, which is nonempty
  exactly when they are; then it is the function of the code's body on
  T (ΛΛ-⋆, by the continuity of Clos3μ terms), and the code finds free
  variable i as get i of T (proj-𝒯).

-}

module Mu.proof.Correctness.Graph.ConcretizeCorrect where

open import proof.Framework.GraphModel.Prelude
open import proof.Framework.GraphModel.DenotProperties using (Every)
open import proof.Framework.GraphModel.Ops
open import proof.Framework.GraphModel.Laws using (⋆-ne)
open import proof.Framework.GraphModel.Env using (Env; •-~)
open import proof.Framework.GraphModel.TypedGraph using (ΛΛ-⋆; 𝒯-ne; 𝒯-intro; proj-𝒯)
open import proof.Framework.GraphModel.TypedOkBase using (fin-code)
open import proof.Semantics.Graph.Prim using (primD-≃)
open import Mu.Language.Type
open import Mu.Language.Clos2
import Mu.Language.Clos3 as T
open import Mu.proof.Semantics.Graph.Clos2 using (⟦_⟧; ⟦_⟧s; fv-env; fv-env-pos)
open import Mu.proof.Semantics.Graph.Clos3 using (ok; con) renaming (⟦_⟧ to ⟦_⟧₃; ⟦_⟧s to ⟦_⟧s₃)
open import Mu.Framework.AllUtil using (All; []; _∷_; pos)
open import Mu.Compiler.Concretize

open import Data.Fin using (Fin; zero; suc)
open import Data.List using (List; []; _∷_; length; replicate)
open import Data.List.Relation.Unary.Any using (here)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Unit.Polymorphic using () renaming (tt to ptt)
open import Level using (lift; lower)
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

𝒯-con : ∀ n (Ys : Results (𝒫 Value) (replicate n ■)) → (∀ j → Con (nthD Ys j)) → Con (𝒯 n Ys)
𝒯-con n Ys c = lower (𝒯-consis n Ys Ys (cs n Ys c))
  where
  cs : ∀ m (Ys : Results (𝒫 Value) (replicate m ■)) → (∀ j → Con (nthD Ys j))
    → results-rel-pres (Every _~_) (replicate m ■) Ys Ys
  cs zero _ _ = ptt
  cs (suc m) ⟨ Y , Ys ⟩ c = ⟨ lift (c zero) , cs m Ys (λ j → c (suc j)) ⟩

cons-con : ∀ {Γ Δ} (Ms : All (T.Tm Γ) Δ) {ρ} → Con-env ρ → ∀ j → Con (nthD (⟦ Ms ⟧s₃ ρ) j)
cons-con (M ∷ Ms) c zero = con M c
cons-con (M ∷ Ms) c (suc j) = cons-con Ms c j

conc : ∀ {Γ Γ' A} (M : Tm Γ A) (φ : Refs Γ Γ') {ρ₂ ρ₃} → Con-env ρ₃ → EnvRel φ ρ₂ ρ₃
  → ⟦ M ⟧ ρ₂ ≃ ⟦ concretize φ M ⟧₃ ρ₃
concs-nth : ∀ {Γ Γ' Δ} (Ms : All (Tm Γ) Δ) (φ : Refs Γ Γ') {ρ₂ ρ₃} → Con-env ρ₃ → EnvRel φ ρ₂ ρ₃
  → ∀ i → nthD (⟦ Ms ⟧s ρ₂) i ≃ nthD (⟦ concs φ Ms ⟧s₃ ρ₃) i

conc (` x) φ c rel = rel x
conc (clos {Δ} N Ms) φ {ρ₂} {ρ₃} c rel =
  ⟨ (λ { w ⟨ ne , w∈ ⟩ → proj₁ (eq (λ i → ne→ i (ne i))) w w∈ })
  , (λ w w∈ → let ne' = 𝒯-ne n (proj₂ (⋆-ne {ΛΛ ⟨ (λ X Y → ⟦ N' ⟧₃ (Y • X • λ _ → ⌈ ω ⌉)) , ptt ⟩} {𝒯 n Es} ⟨ w , w∈ ⟩)) in ⟨ (λ i → ne← i (ne' i)) , proj₂ (eq ne') w w∈ ⟩) ⟩
  where
  n = length Δ
  N' = concretize fv-ref N
  Ds = ⟦ Ms ⟧s ρ₂
  Es = ⟦ concs φ Ms ⟧s₃ ρ₃
  ne→ : ∀ i → nonempty (nthD Ds i) → nonempty (nthD Es i)
  ne→ i ⟨ d , d∈ ⟩ = ⟨ d , proj₁ (concs-nth Ms φ c rel i) d d∈ ⟩
  ne← : ∀ i → nonempty (nthD Es i) → nonempty (nthD Ds i)
  ne← i ⟨ d , d∈ ⟩ = ⟨ d , proj₂ (concs-nth Ms φ c rel i) d d∈ ⟩
  eq : (∀ i → nonempty (nthD Es i))
    → Λ ⟨ (λ Y → ⟦ N ⟧ (Y • fv-env n Ds)) , ptt ⟩ ≃ ⟦ concretize φ (clos N Ms) ⟧₃ ρ₃
  eq ne = ≃-trans (Λ-≃ body) (≃-sym (ΛΛ-⋆ cT (𝒯-intro n ne)
            (λ X⊆ → proj₁ (ok N') (•-~ _⊆_ (•-~ _⊆_ (λ _ _ z → z) X⊆) (λ _ z → z))) (fin-code (ok N') (𝒯-intro n ne))))
    where
    cT = 𝒯-con n Es (cons-con (concs φ Ms) c)
    body : ∀ V → _ → V ≈ V → ⟦ N ⟧ (mem V • fv-env n Ds) ≃ ⟦ N' ⟧₃ (mem V • 𝒯 n Es • λ _ → ⌈ ω ⌉)
    body V _ cV = conc N fv-ref (Con-• (≈⇒Con cV) (Con-• cT (λ _ → Con-⌈⌉ ω)))
      λ { Z → ≃-refl
        ; (S i) → ≃-trans (≃-reflexive (fv-env-pos Ds i))
                    (≃-trans (concs-nth Ms φ c rel (pos i)) (≃-sym (proj-𝒯 n ne (pos i)))) }
conc (app L M) φ c rel = ⋆-≃ (conc L φ c rel) (conc M φ c rel)
conc (lit B k) φ c rel = ≃-refl
conc (tuple {Δ} Ms) φ c rel = 𝒯-≃ (length Δ) (concs-nth Ms φ c rel)
conc (get i M) φ c rel = proj-≃ (pos i) (conc M φ c rel)
conc (inl M) φ c rel = inl-≃ (conc M φ c rel)
conc (inr M) φ c rel = inr-≃ (conc M φ c rel)
conc (case L M N) φ {ρ₂} {ρ₃} c rel =
  𝒞-≃ {F = λ X → ⟦ M ⟧ (X • ρ₂)} {λ X → ⟦ concretize (ext-ref φ) M ⟧₃ (X • ρ₃)}
      {λ X → ⟦ N ⟧ (X • ρ₂)} {λ X → ⟦ concretize (ext-ref φ) N ⟧₃ (X • ρ₃)} (conc L φ c rel)
    (λ v V cV → conc M (ext-ref φ) (Con-• (≈⇒Con cV) c) (rel-ext rel))
    (λ v V cV → conc N (ext-ref φ) (Con-• (≈⇒Con cV) c) (rel-ext rel))
conc (prim p L M) φ c rel = primD-≃ p (conc L φ c rel) (conc M φ c rel)
conc (let′ M N) φ {ρ₂} {ρ₃} c rel =
  letD-≃ {F = λ X → ⟦ N ⟧ (X • ρ₂)} {λ X → ⟦ concretize (ext-ref φ) N ⟧₃ (X • ρ₃)} (conc M φ c rel)
    (λ V _ cV → conc N (ext-ref φ) (Con-• (≈⇒Con cV) c) (rel-ext rel))
conc (fold M) φ c rel = conc M φ c rel
conc (unfold M) φ c rel = conc M φ c rel

concs-nth (M ∷ Ms) φ c rel zero = conc M φ c rel
concs-nth (M ∷ Ms) φ c rel (suc i) = concs-nth Ms φ c rel i

concretize-correct : ∀ {A} (M : Tm [] A) → ⟦ M ⟧ ρ₀ ≃ ⟦ concretize-program M ⟧₃ ρ₀
concretize-correct M = conc M (λ ()) (λ _ → Con-⌈⌉ ω) (λ ())
