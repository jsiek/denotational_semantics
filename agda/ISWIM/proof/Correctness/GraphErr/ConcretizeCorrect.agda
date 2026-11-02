{-

  Correctness of typed concretize (Clos2ᵀ → Clos3ᵀ) in the graph model
  with errors (Semantics/GraphErr/Typed/{Clos2,Clos3}.agda).

  ⟦ M ⟧ ρ₂ ≃ ⟦ concretize φ M ⟧₃ ρ₃ when each variable x of M means in ρ₂
  what its reference φ x (a variable, or a component of a tuple) means
  in ρ₃ (EnvRel), for a consistent ρ₃. Every case but the closure is a
  congruence. Both closures bind their free variables left to right
  (binds-≃₂, binds-assoc); on their values Xs ≃ Ys, the Clos3ᵀ closure is
  its code applied to the tuple T of Ys, which is the function of the
  code's body on T (ΛΛᵐ-⋆, by the continuity of Clos3ᵀ terms), and the
  code finds the free variable i as get i of T (getᵗ-𝒯).

-}

module proof.Correctness.GraphErr.ConcretizeCorrect where

open import proof.Framework.GraphModel.ErrorPrelude
open import proof.Framework.GraphModel.DenotProperties using (Every)
open import proof.Framework.GraphModel.Ops using (𝒯; ⋆; proj; 𝒯-consis)
open import proof.Framework.GraphModel.Env using (Env; •-~)
open import Language.Typed.Type using (Any)
open import Language.Typed.Clos2
import Language.Typed.Clos3 as T
open import Semantics.GraphErr.Typed.Ops using (getᵗ; init)
open import Semantics.GraphErr.Typed.Clos2
open import proof.Semantics.GraphErr.Typed.Clos2
  using (appᵗ-≃; getᵗ-≃; caseᵗ-≃; primᵗ-≃; projectᵗ-≃; ⌊⌋-≃; binds-≃₂; fv-env-nth)
open import proof.Semantics.GraphErr.Typed.Clos3 using (ΛΛᵐ-⋆; ok; con; code-fin) renaming (⟦_⟧ to ⟦_⟧₃; ⟦_⟧s to ⟦_⟧s₃)
open import Compiler.Concretize

open import Data.Fin using (Fin; zero; suc; toℕ)
open import Data.List using (replicate)
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

rel-ext : ∀ {k Γ} {φ : Fin k → Ref Γ} {ρ₂ ρ₃} → EnvRel φ ρ₂ ρ₃ → ∀ {X X'} → X ≃ X'
  → EnvRel (ext-ref φ) (X • ρ₂) (X' • ρ₃)
rel-ext rel X≃ zero = X≃
rel-ext {φ = φ} {ρ₃ = ρ₃} rel {X' = X'} X≃ (suc x) = ≃-trans (rel x) (≃-reflexive (sym (shift-ok (φ x) X' ρ₃)))

{- the components of a tuple of sets of values -}
getᵗ-𝒯 : ∀ n Xs → AllVal n Xs → (i : Fin n) → getᵗ i (𝒯 n Xs) ≃ nthD Xs i
getᵗ-𝒯 (suc n) Xs vs i =
  ≃-trans (≫=-β {F = λ X → proj i ⟨ X , ptt ⟩} (λ X⊆ d → X⊆ (tup[ i ] d)) (𝒯-clean (suc n)) (proj₂ (𝒯-val (suc n) vs)))
    ⟨ (λ { d ⟨ refl , ⟨ d∈ , _ ⟩ ⟩ → d∈ }) , (λ d d∈ → ⟨ refl , ⟨ d∈ , (λ j → proj₂ (vs j)) ⟩ ⟩) ⟩

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

{- The main lemma ---------------------------------------------------------------------}

conc : ∀ {k Γ A} (M : Tm k A) (φ : Fin k → Ref Γ) {ρ₂ ρ₃} → Con-env ρ₃ → EnvRel φ ρ₂ ρ₃
  → ⟦ M ⟧ ρ₂ ≃ ⟦ concretize φ M ⟧₃ ρ₃
concs-nth : ∀ {k Γ n} (Ms : Vec (Tm k Any) n) (φ : Fin k → Ref Γ) {ρ₂ ρ₃} → Con-env ρ₃ → EnvRel φ ρ₂ ρ₃
  → ∀ i → nthD (⟦ Ms ⟧s ρ₂) i ≃ nthD (⟦ concs φ Ms ⟧s₃ ρ₃) i

conc (` x) φ c rel = rel x
conc (clos {n = n} N Ms) φ {ρ₂} {ρ₃} c rel =
  ≃-trans (binds-≃₂ n (concs-nth Ms φ c rel) core) (≃-sym (binds-assoc n (⋆-r {C})))
  where
  N' = concretize fv-ref N
  C = ΛΛᵐ ⟨ (λ X Y → ⟦ N' ⟧₃ (Y • X • λ _ → init)) , ptt ⟩
  core : ∀ {Xs Ys} → (∀ i → nthD Xs i ≃ nthD Ys i × Val (nthD Ys i) × nthD Ys i ⊆ nthD (⟦ concs φ Ms ⟧s₃ ρ₃) i)
    → Λᵐ ⟨ (λ Y → ⟦ N ⟧ (Y • fv-env n Xs)) , ptt ⟩ ≃ (𝒯 n Ys ≫= λ T → ⋆ ⟨ C , ⟨ T , ptt ⟩ ⟩)
  core {Xs} {Ys} r =
    ≃-trans (Λᵐ-≃ body) (≃-sym (≃-trans (≫=-β (⋆-r {C}) (proj₁ vT) (proj₂ vT))
      (ΛΛᵐ-⋆ cT vT (λ X⊆ → proj₁ (ok N') (•-~ _⊆_ (•-~ _⊆_ (λ _ _ z → z) X⊆) (λ _ z → z)))
                   (code-fin N' (proj₂ vT)))))
    where
    vT = 𝒯-val n (λ i → proj₁ (proj₂ (r i)))
    cT = 𝒯-con n Ys (λ j → Con-⊆ (cons-con (concs φ Ms) c j) (proj₂ (proj₂ (r j))))
    body : BodyEq (λ Y → ⟦ N ⟧ (Y • fv-env n Xs)) (λ Y → ⟦ N' ⟧₃ (Y • 𝒯 n Ys • λ _ → init))
    body V _ cV _ = conc N fv-ref (Con-• (≈⇒Con cV) (Con-• cT (λ _ → Con-⌈⌉ ω)))
      λ { zero → ≃-refl
        ; (suc i) → ≃-trans (≃-reflexive (fv-env-nth n Xs i))
                      (≃-trans (proj₁ (r i)) (≃-sym (getᵗ-𝒯 n Ys (λ j → proj₁ (proj₂ (r j))) i))) }
conc (app L M) φ c rel = appᵗ-≃ (conc L φ c rel) (conc M φ c rel)
conc (lit B k) φ c rel = ≃-refl
conc (tuple {n = n} Ms) φ c rel = 𝒯ᵐ-≃ n (concs-nth Ms φ c rel)
conc (get i M) φ c rel = getᵗ-≃ i (conc M φ c rel)
conc (inl M) φ c rel = inlᵐ-≃ (conc M φ c rel)
conc (inr M) φ c rel = inrᵐ-≃ (conc M φ c rel)
conc (case L M N) φ {ρ₂} {ρ₃} c rel =
  caseᵗ-≃ {F = λ X → ⟦ M ⟧ (X • ρ₂)} {λ X → ⟦ concretize (ext-ref φ) M ⟧₃ (X • ρ₃)}
          {λ X → ⟦ N ⟧ (X • ρ₂)} {λ X → ⟦ concretize (ext-ref φ) N ⟧₃ (X • ρ₃)} (conc L φ c rel)
    (λ V _ cV _ → conc M (ext-ref φ) (Con-• (≈⇒Con cV) c) (rel-ext rel ≃-refl))
    (λ V _ cV _ → conc N (ext-ref φ) (Con-• (≈⇒Con cV) c) (rel-ext rel ≃-refl))
conc (prim p L M) φ c rel = primᵗ-≃ p (conc L φ c rel) (conc M φ c rel)
conc (let′ M N) φ {ρ₂} {ρ₃} c rel =
  ≫=-≃ {F = λ X → ⟦ N ⟧ (X • ρ₂)} {λ X → ⟦ concretize (ext-ref φ) N ⟧₃ (X • ρ₃)} (conc M φ c rel)
    (λ _ _ → conc N (ext-ref φ) (Con-• (Con-⊆ (con (concretize φ M) c) ⌊⌋-⊆) c) (rel-ext rel (⌊⌋-≃ (conc M φ c rel))))
conc (inject G M) φ c rel = conc M φ c rel
conc (project G M) φ c rel = projectᵗ-≃ (λ k → k) _ (conc M φ c rel)

concs-nth (M ∷ Ms) φ c rel zero = conc M φ c rel
concs-nth (M ∷ Ms) φ c rel (suc i) = concs-nth Ms φ c rel i

{- The end theorem: every program ------------------------------------------------------}

concretize-correct : ∀ (M : Tm 0 Any) → ⟦ M ⟧ ρ₀ ≃ ⟦ concretize-program M ⟧₃ ρ₀
concretize-correct M = conc M (λ ()) (λ _ → Con-⌈⌉ ω) (λ ())
