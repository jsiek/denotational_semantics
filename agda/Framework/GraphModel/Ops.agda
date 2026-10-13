module Framework.GraphModel.Ops where

open import Framework.Primitives
open import Framework.GraphModel.SetsAsPredicates
open import Framework.abt.Sig using (Sig; ν; ■) public
open import Framework.abt.Var using (Var) public
open import Framework.abt.GSubst using (_•_) public
open import Framework.abt.Sig using (Result)
open import Framework.GraphModel.DOpSig
open import Framework.GraphModel.Domain
open import Framework.GraphModel.OpsBase public

open import Data.Empty renaming (⊥ to False)
open import Data.List using (List ; _∷_ ; []; replicate)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Fin using (Fin; zero; suc)
open import Data.Product using (_×_; Σ; Σ-syntax) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_)
open import Data.Unit renaming (⊤ to True)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; subst)


{- Denotational Operators -----------------------------------------------------}

{- (constants, ℬ, and the components of a tuple of results, nthD, are in
   OpsBase.agda, shared with the graph model with errors) -}

{- \st -}
⋆ : DOp (𝒫 Value) (■ ∷ ■ ∷ [])
⋆ ⟨ D₁ , ⟨ D₂ , _ ⟩ ⟩ w = 
    Σ[ V ∈ List Value ] 
      (V ↦ w ∈ D₁) × (mem V ⊆ D₂) × V ≢ []

pair : DOp (𝒫 Value) (■ ∷ ■ ∷ [])
pair ⟨ D₁ , ⟨ D₂ , _ ⟩ ⟩ ⦅ u , v ⦆ = u ∈ D₁ × v ∈ D₂
pair ⟨ D₁ , ⟨ D₂ , _ ⟩ ⟩ _ = False

car : DOp (𝒫 Value) (■ ∷ [])
car ⟨ D , _ ⟩ u = Σ[ v ∈ Value ] ⦅ u , v ⦆ ∈ D

cdr : DOp (𝒫 Value) (■ ∷ [])
cdr ⟨ D , _ ⟩ v = Σ[ u ∈ Value ] ⦅ u , v ⦆ ∈ D

𝒯 : ∀ (n : ℕ) → DOp (𝒫 Value) (replicate n ■)
𝒯 zero Ds ⟨⟩ = True
{- tuples are strict: a tuple has a value only when all of its components do -}
𝒯 (suc n) Ds (tup[_]_ {n'} i d) =
  Σ[ n≡ ∈ n' ≡ suc n ] d ∈ (nthD Ds (subst Fin n≡ i)) × (∀ j → nonempty (nthD Ds j))
𝒯 n Ds d = False

proj : ∀ {n} → Fin n → DOp (𝒫 Value) (■ ∷ [])
proj i ⟨ D , _ ⟩ d = (tup[ i ] d) ∈ D

inl : DOp (𝒫 Value) (■ ∷ [])
inl ⟨ D , _ ⟩ (left v) = v ∈ D
inl ⟨ D , _ ⟩ _ = False

inr : DOp (𝒫 Value) (■ ∷ [])
inr ⟨ D , _ ⟩ (right v) = v ∈ D
inr ⟨ D , _ ⟩ _ = False

{- the binders, 𝒞 and Λ, bind only finite, nonempty, consistent sets
   (V ≈ V), so that no denotation under a consistent environment holds
   inconsistent elements -}
𝒞 : DOp (𝒫 Value) (■ ∷ ν ■ ∷ ν ■ ∷ [])
𝒞 ⟨ D , ⟨ E , ⟨ F , _ ⟩ ⟩ ⟩ w =
    Σ[ v ∈ Value ] Σ[ V ∈ List Value ] (∀ d → d ∈ mem (v ∷ V) → left d ∈ D) × w ∈ E (mem (v ∷ V)) × (v ∷ V) ≈ (v ∷ V)
  ⊎ Σ[ v ∈ Value ] Σ[ V ∈ List Value ] (∀ d → d ∈ mem (v ∷ V) → right d ∈ D) × w ∈ F (mem (v ∷ V)) × (v ∷ V) ≈ (v ∷ V)

Λ : DOp (𝒫 Value) (ν ■ ∷ [])
Λ ⟨ f , _ ⟩ (V ↦ w) = w ∈ f (mem V) × V ≢ [] × V ≈ V
Λ ⟨ f , _ ⟩ ν = True
Λ ⟨ f , _ ⟩ d = False

{- D, provided that each of the n sets in Ds is nonempty (for strict closures) -}
guard-n : ∀ n → Results (𝒫 Value) (replicate n ■) → 𝒫 Value → 𝒫 Value
guard-n n Ds D w = (∀ i → nonempty (nthD Ds i)) × w ∈ D
