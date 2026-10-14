{-

  Lemmas about the semantics of Clos2ᵀ in the graph model with errors
  (Semantics/GraphErr/Typed/Clos2.agda), and about the typed operators it
  shares with ISWIMᵀ and Clos3ᵀ (Semantics/GraphErr/Typed/Ops.agda):

  * the typed operators are the error monad's kernels under binds, with
    no check, so they are Good (monotone, consistent, continuous) by the
    combinators of proof/Framework/GraphModel/ErrorMonad.agda; hence
    their congruences;
  * n binds of sets of values, or of equal operands (binds-val-≃,
    binds-≃₂);
  * the environment of the code of a closure (fv-env-nth).

-}

module proof.Semantics.GraphErr.Typed.Clos2 where

open import Semantics.GraphErr.Typed.Clos2 public

open import proof.Framework.GraphModel.SetsAsPredicates
open import proof.Framework.GraphModel.DOpSig
open import proof.Framework.GraphModel.Domain
open import proof.Framework.GraphModel.OpsBase
open import proof.Framework.GraphModel.Continuity using (⋆-good; proj-good; 𝒞-good)
open import proof.Framework.GraphModel.ContinuityBase using (Good; mono; mk-good)
open import proof.Framework.GraphModel.ErrorMonad
open import proof.Semantics.Graph.Prim using (primD-good)
open import Language.Typed.Type using (Flat)
open import Semantics.GraphErr.Typed.Ops

open import Data.Fin using (Fin; zero; suc; toℕ)
open import Data.List using (_∷_; []; replicate)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Sum using (inj₂)
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
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

project-good : ∀ k → Good ⊤ (■ ∷ []) (λ Ds → projectᵗ k (proj₁ Ds))
project-good k = strict-good (mk-good (λ { _ _ ⟨ lift X⊆ , _ ⟩ → lift (checked-mono X⊆ (⇂-mono X⊆)) })
  (λ { _ _ ⟨ lift X~ , _ ⟩ → lift (checked-consis X~ (⇂-~ X~) needs needs) })
  (λ { _ NE ⟨ ⟨ _ , c ⟩ , _ ⟩ → checked-cont c (⇂-cont c) }))
  where needs : ∀ {X} → Needs k X (X ⇂ λ d → kind d ≡ k)
        needs w ⟨ w∈ , wk ⟩ = inj₂ ⟨ w , ⟨ w∈ , wk ⟩ ⟩

⌊⌋-≃ : ∀ {D D'} → D ≃ D' → ⌊ D ⌋ ≃ ⌊ D' ⌋
⌊⌋-≃ D≃ = ⟨ ⌊⌋-mono (proj₁ D≃) , ⌊⌋-mono (proj₂ D≃) ⟩

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

projectᵗ-≃ : ∀ k {D D'} → D ≃ D' → projectᵗ k D ≃ projectᵗ k D'
projectᵗ-≃ k D≃ = mono-≃ (mono (project-good k)) ⟨ lift D≃ , ptt ⟩

{- n binds ------------------------------------------------------------------------}

{- of sets of values: the continuation, on sets equal to them -}
binds-val-≃ : ∀ n {Ds K A} → AllVal n Ds → (∀ {Xs} → (∀ i → nthD Xs i ≃ nthD Ds i) → K Xs ≃ A) → binds n Ds K ≃ A
binds-val-≃ zero _ h = h (λ ())
binds-val-≃ (suc n) {⟨ D , Ds ⟩} {K} vs h =
  ≃-trans (≫=-val-β {F = λ X → binds n Ds (λ Xs → K ⟨ X , Xs ⟩)} (vs zero))
    (binds-val-≃ n (λ i → vs (suc i)) λ r → h λ { zero → ⟨ ⌊⌋-⊆ , ⌊⌋-clean (proj₁ (vs zero)) ⟩ ; (suc i) → r i })

{- of equal operands, into continuations equal on equal values -}
binds-≃₂ : ∀ n {Ds Es K K'} → (∀ i → nthD Ds i ≃ nthD Es i)
  → (∀ {Xs Ys} → (∀ i → nthD Xs i ≃ nthD Ys i × Val (nthD Ys i) × nthD Ys i ⊆ nthD Es i) → K Xs ≃ K' Ys)
  → binds n Ds K ≃ binds n Es K'
binds-≃₂ zero _ h = h (λ ())
binds-≃₂ (suc n) {⟨ D , Ds ⟩} {⟨ E , Es ⟩} {K} {K'} eq h =
  ≫=-≃ {F = λ X → binds n Ds (λ Xs → K ⟨ X , Xs ⟩)} {λ X → binds n Es (λ Xs → K' ⟨ X , Xs ⟩)} (eq zero) λ _ c → binds-≃₂ n (λ i → eq (suc i))
    λ r → h λ { zero → ⟨ ⌊⌋-≃ (eq zero) , ⟨ ⌊⌋-val c , ⌊⌋-⊆ ⟩ ⟩ ; (suc i) → r i }

{- The code of a closure ----------------------------------------------------------}

fv-env-nth : ∀ n Xs (i : Fin n) → fv-env n Xs (toℕ i) ≡ nthD Xs i
fv-env-nth (suc n) ⟨ X , Xs ⟩ zero = refl
fv-env-nth (suc n) ⟨ X , Xs ⟩ (suc i) = fv-env-nth n Xs i
