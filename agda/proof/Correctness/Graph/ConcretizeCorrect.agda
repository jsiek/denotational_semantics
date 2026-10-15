{-

  Correctness of typed concretize (Clos2ᵀ → Clos3ᵀ) in the graph model
  (Semantics/Graph/Typed/{Clos2,Clos3}.agda).

  ⟦ M ⟧ ρ₂ ≃ ⟦ concretize φ M ⟧₃ ρ₃ when each variable x of M means in ρ₂
  what its reference φ x (a variable, or a component of a tuple) means
  in ρ₃ (EnvRel), for a consistent ρ₃. Every case but the closure is a
  congruence. A Clos2ᵀ closure is strict in its free variables, and a
  Clos3ᵀ closure is its code applied to their tuple T, which is nonempty
  exactly when they are; then it is the function of the code's body on
  T (ΛΛ-⋆, by the continuity of Clos3ᵀ terms), and the code finds free
  variable i as get i of T (proj-𝒯).

-}

module proof.Correctness.Graph.ConcretizeCorrect where

open import proof.Framework.GraphModel.Prelude
open import proof.Framework.GraphModel.DenotProperties using (Every)
open import proof.Framework.GraphModel.Ops
open import proof.Framework.GraphModel.Laws using (⋆-ne)
open import proof.Framework.GraphModel.Env using (Env; •-~)
open import proof.Framework.GraphModel.TypedGraph using (ΛΛ-⋆; 𝒯-ne; 𝒯-intro; proj-𝒯)
open import proof.Framework.GraphModel.TypedOkBase using (fin-code)
open import proof.Semantics.Graph.Prim using (primD-≃)
open import Language.Typed.Type using (Any)
open import Language.Typed.Clos2
import Language.Typed.Clos3 as T
open import proof.Semantics.Graph.Typed.Ops using (project-≃; init)
open import proof.Semantics.Graph.Typed.Clos2 using (⟦_⟧; ⟦_⟧s; fv-env; fv-env-nth)
open import proof.Semantics.Graph.Typed.Clos3 using (ok; con) renaming (⟦_⟧ to ⟦_⟧₃; ⟦_⟧s to ⟦_⟧s₃)
open import Compiler.Concretize

open import Data.Fin using (Fin; zero; suc; toℕ)
open import Data.List using (replicate)
open import Data.List.Relation.Unary.Any using (here)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Vec using (Vec; []; _∷_)
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Unit.Polymorphic using () renaming (tt to ptt)
open import Level using (lift; lower)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)

{- each variable means what its reference means -}
EnvRel : ∀ {k Γ} → (Fin k → Ref Γ) → Env Value → Env Value → Set
EnvRel φ ρ₂ ρ₃ = ∀ x → ρ₂ (toℕ x) ≃ ⟦ ref-tm (φ x) ⟧₃ ρ₃

shift-ok : ∀ {Γ A} (r : Ref Γ) X ρ → ⟦ ref-tm (shift-ref {A = A} r) ⟧₃ (X • ρ) ≡ ⟦ ref-tm r ⟧₃ ρ
shift-ok (var x) X ρ = refl
shift-ok (prj i x) X ρ = refl

rel-ext : ∀ {k Γ} {φ : Fin k → Ref Γ} {ρ₂ ρ₃} → EnvRel φ ρ₂ ρ₃ → ∀ {X} → EnvRel (ext-ref φ) (X • ρ₂) (X • ρ₃)
rel-ext rel zero = ≃-refl
rel-ext {φ = φ} {ρ₃ = ρ₃} rel {X} (suc x) = ≃-trans (rel x) (≃-reflexive (sym (shift-ok (φ x) X ρ₃)))

𝒯-con : ∀ n (Ys : Results (𝒫 Value) (replicate n ■)) → (∀ j → Con (nthD Ys j)) → Con (𝒯 n Ys)
𝒯-con n Ys c = lower (𝒯-consis n Ys Ys (cs n Ys c))
  where
  cs : ∀ m (Ys : Results (𝒫 Value) (replicate m ■)) → (∀ j → Con (nthD Ys j))
    → results-rel-pres (Every _~_) (replicate m ■) Ys Ys
  cs zero _ _ = ptt
  cs (suc m) ⟨ Y , Ys ⟩ c = ⟨ lift (c zero) , cs m Ys (λ j → c (suc j)) ⟩

cons-con : ∀ {Γ n} (Ms : Vec (T.Tm Γ Any) n) {ρ} → Con-env ρ → ∀ j → Con (nthD (⟦ Ms ⟧s₃ ρ) j)
cons-con (M ∷ Ms) c zero = con M c
cons-con (M ∷ Ms) c (suc j) = cons-con Ms c j

conc : ∀ {k Γ A} (M : Tm k A) (φ : Fin k → Ref Γ) {ρ₂ ρ₃} → Con-env ρ₃ → EnvRel φ ρ₂ ρ₃
  → ⟦ M ⟧ ρ₂ ≃ ⟦ concretize φ M ⟧₃ ρ₃
concs-nth : ∀ {k Γ n} (Ms : Vec (Tm k Any) n) (φ : Fin k → Ref Γ) {ρ₂ ρ₃} → Con-env ρ₃ → EnvRel φ ρ₂ ρ₃
  → ∀ i → nthD (⟦ Ms ⟧s ρ₂) i ≃ nthD (⟦ concs φ Ms ⟧s₃ ρ₃) i

conc (` x) φ c rel = rel x
conc (clos {n = n} N Ms) φ {ρ₂} {ρ₃} c rel =
  ⟨ (λ { w ⟨ ne , w∈ ⟩ → proj₁ (eq (λ i → ne→ i (ne i))) w w∈ })
  , (λ w w∈ → let ne' = 𝒯-ne n (proj₂ (⋆-ne {ΛΛ ⟨ (λ X Y → ⟦ N' ⟧₃ (Y • X • λ _ → init)) , ptt ⟩} {𝒯 n Es} ⟨ w , w∈ ⟩)) in ⟨ (λ i → ne← i (ne' i)) , proj₂ (eq ne') w w∈ ⟩) ⟩
  where
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
    body : ∀ V → _ → V ≈ V → ⟦ N ⟧ (mem V • fv-env n Ds) ≃ ⟦ N' ⟧₃ (mem V • 𝒯 n Es • λ _ → init)
    body V _ cV = conc N fv-ref (Con-• (≈⇒Con cV) (Con-• cT (λ _ → Con-⌈⌉ ω)))
      λ { zero → ≃-refl
        ; (suc i) → ≃-trans (≃-reflexive (fv-env-nth n Ds i))
                      (≃-trans (concs-nth Ms φ c rel i) (≃-sym (proj-𝒯 n ne i))) }
conc (app L M) φ c rel = ⋆-≃ (conc L φ c rel) (conc M φ c rel)
conc (lit B k) φ c rel = ≃-refl
conc (tuple {n = n} Ms) φ c rel = 𝒯-≃ n (concs-nth Ms φ c rel)
conc (get i M) φ c rel = proj-≃ i (conc M φ c rel)
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
conc (inject G M) φ c rel = conc M φ c rel
conc (project t M) φ c rel = project-≃ _ t (conc M φ c rel)

concs-nth (M ∷ Ms) φ c rel zero = conc M φ c rel
concs-nth (M ∷ Ms) φ c rel (suc i) = concs-nth Ms φ c rel i

concretize-correct : ∀ (M : Tm 0 Any) → ⟦ M ⟧ ρ₀ ≃ ⟦ concretize-program M ⟧₃ ρ₀
concretize-correct M = conc M (λ ()) (λ _ → Con-⌈⌉ ω) (λ ())
