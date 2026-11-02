{-

  Lemmas about the semantics of Clos2ᵀ in the graph model with errors
  (Semantics/GraphErr/Typed/Clos2.agda), and about the typed operators it
  shares with ISWIMᵀ and Clos3ᵀ (Semantics/GraphErr/Typed/Ops.agda):

  * the typed operators are the error monad's kernels under binds, with
    no check, so they are Good (monotone, consistent, continuous) by the
    combinators of proof/Framework/GraphModel/ErrorMonad.agda; hence
    their congruences (with ⌊⌋-≃, binds-val-≃ and binds-≃₂, of any
    typed language, proof/Framework/GraphModel/TypedBinders.agda);
  * the environment of the code of a closure (fv-env-nth).

-}

module proof.Semantics.GraphErr.Typed.Clos2 where

open import Semantics.GraphErr.Typed.Clos2 public
open import proof.Framework.GraphModel.TypedBinders using (⌊⌋-≃; binds-val-≃; binds-≃₂) public
open import proof.Framework.GraphModel.TypedOk using (check-kind-good)

open import proof.Framework.GraphModel.ErrorPrelude
open import proof.Framework.GraphModel.Continuity using (⋆-good; proj-good; 𝒞-good)
open import proof.Framework.GraphModel.ContinuityBase using (Good; mono; VEnv; Cont; Approx; env; one; approx-init)
open import proof.Framework.GraphModel.Env using (nonempty-env)
open import proof.Semantics.Graph.Prim using (primD-good)
open import Language.Typed.Type using (Flat; Tag; ttup; tfun; tsum; tint; flat)
open import Semantics.GraphErr.Typed.Ops

open import Data.Fin using (Fin; zero; suc; toℕ)
open import Data.List using (_∷_; [])
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (proj₁; proj₂; Σ-syntax) renaming (_,_ to ⟨_,_⟩)
open import Data.Unit using (⊤)
open import Data.Unit.Polymorphic using () renaming (tt to ptt)
open import Level using (lift)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

{- The typed operators -------------------------------------------------------------}

app-good : Good ⊤ (■ ∷ ■ ∷ []) (λ Ds → appᵗ (proj₁ Ds) (proj₁ (proj₂ Ds)))
app-good = strict-good (strict₂-good ⋆-good)

get-good : ∀ {n} (i : Fin n) → Good ⊤ (■ ∷ []) (λ Ds → getᵗ i (proj₁ Ds))
get-good i = strict-good (proj-good i)

case-good : Good ⊤ (■ ∷ ν ■ ∷ ν ■ ∷ []) (λ Ds → caseᵗ (proj₁ Ds) (proj₁ (proj₂ Ds)) (proj₁ (proj₂ (proj₂ Ds))))
case-good = strict-good (in⇂-good {Q = ValPayload} 𝒞-good)

prim-good : ∀ p → Good ⊤ (■ ∷ ■ ∷ []) (λ Ds → primᵗ p (proj₁ Ds) (proj₁ (proj₂ Ds)))
prim-good p = strict-good (strict₂-good (primD-good p))

hit-mono : ∀ t {X X'} → X ⊆ X' → hit t X → hit t X'
hit-mono (ttup n i) X⊆ ⟨ e , e∈ ⟩ = ⟨ e , X⊆ _ e∈ ⟩
hit-mono tfun _ h = h
hit-mono tsum _ h = h
hit-mono tint _ h = h

hit-fin : ∀ t {X : VEnv → 𝒫 Value} {ρ} → nonempty-env ρ → Cont X ρ → hit t (X ρ) → Σ[ a ∈ Approx ρ ] hit t (X (env a))
hit-fin (ttup n i) {X} NE c ⟨ e , e∈ ⟩ = let ⟨ a , e∈′ ⟩ = one X c e∈ in ⟨ a , ⟨ e , e∈′ ⟩ ⟩
hit-fin tfun NE c h = ⟨ approx-init NE , h ⟩
hit-fin tsum NE c h = ⟨ approx-init NE , h ⟩
hit-fin tint NE c h = ⟨ approx-init NE , h ⟩

project-good : ∀ φ t → Good ⊤ (■ ∷ []) (λ Ds → projectᵠ φ t (proj₁ Ds))
project-good φ t = strict-good (check-kind-good (hit t) (hit-mono t) (hit-fin t) φ (kindᶠ (flat t)))

appᵗ-≃ : ∀ {D D' E E'} → D ≃ D' → E ≃ E' → appᵗ D E ≃ appᵗ D' E'
appᵗ-≃ D≃ E≃ = mono-≃ (mono app-good) ⟨ lift D≃ , ⟨ lift E≃ , ptt ⟩ ⟩

getᵗ-≃ : ∀ {n} (i : Fin n) {D D'} → D ≃ D' → getᵗ i D ≃ getᵗ i D'
getᵗ-≃ i D≃ = mono-≃ (mono (get-good i)) ⟨ lift D≃ , ptt ⟩

primᵗ-≃ : ∀ p {D D' E E'} → D ≃ D' → E ≃ E' → primᵗ p D E ≃ primᵗ p D' E'
primᵗ-≃ p D≃ E≃ = mono-≃ (mono (prim-good p)) ⟨ lift D≃ , ⟨ lift E≃ , ptt ⟩ ⟩

caseᵗ-≃ : ∀ {D D' F F' G G'} → D ≃ D' → BodyEq F F' → BodyEq G G' → caseᵗ D F G ≃ caseᵗ D' F' G'
caseᵗ-≃ {F = F} {F'} {G} {G'} D≃ F≃ G≃ =
  ⟨ ≫=-mono (proj₁ D≃) (λ X⊆ → 𝒞⇂-⊆ {A = F} {F'} {G} {G'} X⊆ (λ V a b c → proj₁ (F≃ V a b c)) (λ V a b c → proj₁ (G≃ V a b c)))
  , ≫=-mono (proj₂ D≃) (λ X⊆ → 𝒞⇂-⊆ {A = F'} {F} {G'} {G} X⊆ (λ V a b c → proj₂ (F≃ V a b c)) (λ V a b c → proj₂ (G≃ V a b c))) ⟩

projectᵗ-≃ : ∀ φ t {D D'} → D ≃ D' → projectᵠ φ t D ≃ projectᵠ φ t D'
projectᵗ-≃ φ t D≃ = mono-≃ (mono (project-good φ t)) ⟨ lift D≃ , ptt ⟩

{- The code of a closure ----------------------------------------------------------}

fv-env-nth : ∀ n Xs (i : Fin n) → fv-env n Xs (toℕ i) ≡ nthD Xs i
fv-env-nth (suc n) ⟨ X , Xs ⟩ zero = refl
fv-env-nth (suc n) ⟨ X , Xs ⟩ (suc i) = fv-env-nth n Xs i
