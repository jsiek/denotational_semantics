{-

  Scott domains: a property of the elements of a sum Σᵈ T G
  (Framework/Scott/Sum.agda) that holds of each element of a directed
  family holds of its sup, provided that it is closed under directed
  sups in each summand: the sup of a directed family is in the summand
  of its common tag, the sup there of the family carried along the
  equations of its tags.

-}

open import MLTT.Spartan
open import UF.FunExt
open import UF.PropTrunc
open import UF.Subsingletons
open import UF.Sets

module proof.Framework.Scott.Sum
        (pt : propositional-truncations-exist)
        (fe : Fun-Ext)
       where

open import Framework.Scott.Base pt fe
open import Framework.Scott.Sum pt fe

module _ (T : 𝓤₀ ̇ ) (T-is-set : is-set T) (G : T → DCPO₁) where

 Σ-sup-ind : {𝓦 : Universe} (Q : (t : T) → ⟨ G t ⟩ → 𝓦 ̇ )
   → ((t : T) {I : 𝓤₀ ̇ } (β : I → ⟨ G t ⟩) (δ : is-Directed (G t) β) → ((i : I) → Q t (β i)) → Q t (∐ (G t) {I} {β} δ))
   → {I : 𝓤₀ ̇ } (α : I → ⟨ Σᵈ T T-is-set G ⟩) (δ : is-Directed (Σᵈ T T-is-set G) α)
   → ((i : I) → Q (pr₁ (α i)) (pr₂ (α i)))
   → Q (pr₁ (∐ (Σᵈ T T-is-set G) {I} {α} δ)) (pr₂ (∐ (Σᵈ T T-is-set G) {I} {α} δ))
 Σ-sup-ind Q Q-sup α δ h =
  Q-sup (tag T T-is-set G α δ) (in-summand T T-is-set G α δ) (in-summand-is-directed T T-is-set G α δ)
    (λ i → tr-Q (tag-eq T T-is-set G α δ i) (h i))
  where
   tr-Q : {s t : T} (e : s ＝ t) {x : ⟨ G s ⟩} → Q s x → Q t (transport (λ t → ⟨ G t ⟩) e x)
   tr-Q refl q = q
