{-

  Laws of the graph model's operators that the proofs of the typed
  passes use (language independent):

  * a let whose body needs one element of the bound set (let-single);
  * code, a closed function of two arguments (ΛΛ), applied to an
    environment T: the function of its body on T (ΛΛ-⋆);
  * a tuple is nonempty exactly when its components are (𝒯-ne, 𝒯-intro),
    and then its component i is the i-th set (proj-𝒯);
  * a strict closure's guard (guard-n) holds on nonempty sets.

-}

module proof.Framework.GraphModel.TypedGraph where

open import proof.Framework.GraphModel.SetsAsPredicates
open import proof.Framework.GraphModel.DOpSig
open import proof.Framework.GraphModel.Domain
open import proof.Framework.GraphModel.Ops

open import Data.Fin using (Fin; zero; suc)
open import Data.List using (List; []; _∷_; replicate)
open import Data.List.Relation.Unary.All using (_∷_; [])
open import Data.List.Relation.Unary.Any using (here)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; proj₁; proj₂; Σ-syntax) renaming (_,_ to ⟨_,_⟩)
open import Data.Unit using (tt)
open import Data.Unit.Polymorphic using () renaming (tt to ptt)
open import Relation.Binary.PropositionalEquality using (_≢_; refl)

single-≈ : ∀ d → (d ∷ []) ≈ (d ∷ [])
single-≈ d = ⟨ ~-refl d ∷ [] , tt ⟩

{- a let whose body needs only one element of the bound set -}
let-single : ∀ {F D} → Mono₁ F → (∀ w → w ∈ F D → Σ[ d ∈ Value ] d ∈ D × w ∈ F (mem (d ∷ [])))
  → letD ⟨ D , ⟨ F , ptt ⟩ ⟩ ≃ F D
let-single m one =
  ⟨ (λ { w ⟨ V , ⟨ ⟨ w∈ , _ ⟩ , ⟨ V⊆ , _ ⟩ ⟩ ⟩ → m V⊆ w w∈ })
  , (λ w w∈ → let ⟨ d , ⟨ d∈ , w∈′ ⟩ ⟩ = one w w∈ in
       ⟨ d ∷ [] , ⟨ ⟨ w∈′ , ⟨ (λ ()) , single-≈ d ⟩ ⟩ , ⟨ (λ { _ (here refl) → d∈ }) , (λ ()) ⟩ ⟩ ⟩) ⟩

{- code applied to its environment T, when the body uses a finite part of T -}
ΛΛ-⋆ : ∀ {F T} → Con T → nonempty T → (∀ {X X' Y} → X ⊆ X' → F X Y ⊆ F X' Y)
  → (∀ U w → U ≢ [] → w ∈ F T (mem U) → Σ[ V ∈ List Value ] V ≢ [] × mem V ⊆ T × w ∈ F (mem V) (mem U))
  → ⋆ ⟨ ΛΛ ⟨ F , ptt ⟩ , ⟨ T , ptt ⟩ ⟩ ≃ Λ ⟨ F T , ptt ⟩
ΛΛ-⋆ {F} {T} cT ⟨ t , t∈ ⟩ m fin = ⟨ H , G ⟩
  where
  G : Λ ⟨ F T , ptt ⟩ ⊆ ⋆ ⟨ ΛΛ ⟨ F , ptt ⟩ , ⟨ T , ptt ⟩ ⟩
  G ν _ = ⟨ t ∷ [] , ⟨ ⟨ tt , ⟨ (λ ()) , single-≈ t ⟩ ⟩ , ⟨ (λ { _ (here refl) → t∈ }) , (λ ()) ⟩ ⟩ ⟩
  G (U ↦ x) ⟨ x∈ , ⟨ neU , cU ⟩ ⟩ with fin U x neU x∈
  ... | ⟨ V , ⟨ neV , ⟨ V⊆ , x∈′ ⟩ ⟩ ⟩ =
    ⟨ V , ⟨ ⟨ ⟨ x∈′ , ⟨ neU , cU ⟩ ⟩ , ⟨ neV , Con⇒≈ V cT V⊆ ⟩ ⟩ , ⟨ V⊆ , neV ⟩ ⟩ ⟩
  H : ⋆ ⟨ ΛΛ ⟨ F , ptt ⟩ , ⟨ T , ptt ⟩ ⟩ ⊆ Λ ⟨ F T , ptt ⟩
  H ν _ = tt
  H (U ↦ x) ⟨ V , ⟨ ⟨ ⟨ x∈ , r ⟩ , _ ⟩ , ⟨ V⊆T , _ ⟩ ⟩ ⟩ = ⟨ m V⊆T x x∈ , r ⟩

{- Tuples ---------------------------------------------------------------------------}

𝒯-ne : ∀ n {Ds} → nonempty (𝒯 n Ds) → ∀ i → nonempty (nthD Ds i)
𝒯-ne (suc n) ⟨ tup[ i ] d , ⟨ refl , ⟨ _ , ne ⟩ ⟩ ⟩ = ne

𝒯-intro : ∀ n {Ds} → (∀ i → nonempty (nthD Ds i)) → nonempty (𝒯 n Ds)
𝒯-intro zero ne = ⟨ ⟨⟩ , tt ⟩
𝒯-intro (suc n) ne = ⟨ tup[ zero ] proj₁ (ne zero) , ⟨ refl , ⟨ proj₂ (ne zero) , ne ⟩ ⟩ ⟩

proj-𝒯 : ∀ n {Ds} → (∀ j → nonempty (nthD Ds j)) → (i : Fin n) → proj i ⟨ 𝒯 n Ds , ptt ⟩ ≃ nthD Ds i
proj-𝒯 (suc n) ne i = ⟨ (λ { d ⟨ refl , ⟨ d∈ , _ ⟩ ⟩ → d∈ }) , (λ d d∈ → ⟨ refl , ⟨ d∈ , ne ⟩ ⟩) ⟩

{- a strict closure's guard -}
guard-≃ : ∀ n m {Ds Es D E} → ((∀ i → nonempty (nthD Ds i)) → (∀ i → nonempty (nthD Es i)))
  → ((∀ i → nonempty (nthD Es i)) → (∀ i → nonempty (nthD Ds i)))
  → ((∀ i → nonempty (nthD Ds i)) → D ≃ E) → guard-n n Ds D ≃ guard-n m Es E
guard-≃ n m f g e = ⟨ (λ { w ⟨ ne , w∈ ⟩ → ⟨ f ne , proj₁ (e ne) w w∈ ⟩ })
                  , (λ { w ⟨ ne , w∈ ⟩ → ⟨ g ne , proj₂ (e (g ne)) w w∈ ⟩ }) ⟩
