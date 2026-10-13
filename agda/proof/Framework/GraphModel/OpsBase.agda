{-

  The lemmas about the operators that the graph model and the graph
  model with errors share unchanged (Framework/GraphModel/OpsBase.agda):
  constants and the components of a tuple of results; and the finitary
  functions of the β laws.

-}

module proof.Framework.GraphModel.OpsBase where

open import Framework.GraphModel.OpsBase public

open import Framework.Primitives
open import proof.Framework.GraphModel.SetsAsPredicates
open import Framework.Syntax.SigUtil
open import proof.Framework.GraphModel.DOpSig
open import proof.Framework.GraphModel.DOpSig public using (RR; RRs; RRs-refl; rr-trans; mono⇒≃; mono-≃)
open import proof.Framework.GraphModel.DenotProperties
open import proof.Framework.GraphModel.Domain

open import Data.Empty using (⊥-elim) renaming (⊥ to False)
open import Data.List using (List ; _∷_ ; []; _++_; length; replicate)
open import Data.List.Relation.Unary.Any using (Any; here; there)
open import Data.List.Membership.Propositional.Properties using (∈-++⁺ˡ; ∈-++⁺ʳ; ∈-++⁻)
open import Data.Nat using (ℕ; zero; suc; _≟_; _<_; z≤n; s≤s; _+_)
open import Data.Fin using (Fin; zero; suc)
open import Data.Fin.Properties using () renaming (_≟_ to _fin≟_)
open import Data.Product using (_×_; Σ; Σ-syntax; proj₁; proj₂; ∃; ∃-syntax)
    renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_])
open import Data.Unit using (tt) renaming (⊤ to True)
open import Data.Unit.Polymorphic using (⊤) renaming (tt to ptt)
open import Relation.Binary.PropositionalEquality
    using (_≡_; _≢_; refl; sym; trans; subst)
open import Level using (Level; Lift; lift; lower)
    renaming (zero to lzero; suc to lsuc)
open import Relation.Nullary using (¬_; Dec; yes; no)


{- Constants ---------------------------------------------------------------------}

ℬ-mono : ∀ B k → monotone [] ■ (ℬ B k)
ℬ-mono B k _ _ _ = lift (λ d d∈ → d∈)

ℬ-consis : ∀ B k → consistent _~_ [] ■ (ℬ B k)
ℬ-consis B k _ _ _ = lift G
  where
  G : Every _~_ (ℬ B k ptt) (ℬ B k ptt)
  G (const {B'} k) (const {B''} k') ⟨ refl , d∈ ⟩  ⟨ refl , d'∈ ⟩ = ⟨ refl , trans (sym d∈) d'∈ ⟩

{- Components of a tuple of results ----------------------------------------------}

nthD-mono : ∀ {n} (Ds Es : Results (𝒫 Value) (replicate n ■))
  → results-rel-pres _⊆_ (replicate n ■) Ds Es → (i : Fin n) → nthD Ds i ⊆ nthD Es i
nthD-mono {suc n} ⟨ D , Ds ⟩ ⟨ E , Es ⟩ ⟨ lift D⊆ , _ ⟩ zero = D⊆
nthD-mono {suc n} ⟨ D , Ds ⟩ ⟨ E , Es ⟩ ⟨ _ , Ds⊆ ⟩ (suc i) = nthD-mono Ds Es Ds⊆ i

nthD-consis : ∀ {n} (Ds Es : Results (𝒫 Value) (replicate n ■))
  → results-rel-pres (Every _~_) (replicate n ■) Ds Es
  → (i : Fin n) → Every _~_ (nthD Ds i) (nthD Es i)
nthD-consis {suc n} ⟨ D , Ds ⟩ ⟨ E , Es ⟩ ⟨ lift D~ , _ ⟩ zero = D~
nthD-consis {suc n} ⟨ D , Ds ⟩ ⟨ E , Es ⟩ ⟨ _ , Ds~ ⟩ (suc i) = nthD-consis Ds Es Ds~ i

nthD-≃ : ∀ {n} (Ds Es : Results (𝒫 Value) (replicate n ■)) → RRs (replicate n ■) Ds Es
  → ∀ i → nthD Ds i ≃ nthD Es i
nthD-≃ {suc n} ⟨ D , Ds ⟩ ⟨ E , Es ⟩ ⟨ D≃ , _ ⟩ zero = lower D≃
nthD-≃ {suc n} ⟨ D , Ds ⟩ ⟨ E , Es ⟩ ⟨ _ , Ds≃ ⟩ (suc i) = nthD-≃ Ds Es Ds≃ i

nthD⇒RRs : ∀ {n} (Ds Es : Results (𝒫 Value) (replicate n ■)) → (∀ i → nthD Ds i ≃ nthD Es i)
  → RRs (replicate n ■) Ds Es
nthD⇒RRs {zero} _ _ _ = ptt
nthD⇒RRs {suc n} ⟨ D , Ds ⟩ ⟨ E , Es ⟩ eq = ⟨ lift (eq zero) , nthD⇒RRs Ds Es (λ i → eq (suc i)) ⟩

{- Finitary functions of a set ---------------------------------------------------}

Mono₁ : (𝒫 Value → 𝒫 Value) → Set₁
Mono₁ F = ∀ {X Y} → X ⊆ Y → F X ⊆ F Y

{- each element of F X needs only a finite, nonempty part of X -}
Finitary : (𝒫 Value → 𝒫 Value) → 𝒫 Value → Set
Finitary F X = ∀ w → w ∈ F X → Σ[ V ∈ List Value ] V ≢ [] × mem V ⊆ X × w ∈ F (mem V)

