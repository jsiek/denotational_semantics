{-

  Scott domains: a property of the values of the elements of a directed
  family in a lifting 𝓛ᵈ A holds of the value of its sup, if it is
  closed under directed sups in A: the sup is defined only if some
  element is, and its value is the sup of the values of the defined
  elements. (is-defined l and value l are written pr₁ l and pr₁ (pr₂ l)
  here, which lets Agda infer their implicit arguments.)

-}

open import MLTT.Spartan hiding (J)
open import UF.FunExt
open import UF.PropTrunc
open import UF.Subsingletons

module proof.Framework.Scott.Lift
        (pt : propositional-truncations-exist)
        (fe : Fun-Ext)
        (pe : propext 𝓤₀)
       where

open import Framework.Scott.Base pt fe
open import Framework.Scott.Lift pt fe pe
open import Lifting.Miscelanea 𝓤₀ using (value-is-constant)

module _ (A : DCPO₁) {I : 𝓤₀ ̇ } (α : I → ⟨ 𝓛ᵈ A ⟩) (δ : is-Directed (𝓛ᵈ A) α) where

 private
  s : ⟨ 𝓛ᵈ A ⟩
  s = ∐ (𝓛ᵈ A) {I} {α} δ
  J = Σ i ꞉ I , pr₁ (α i)
  β : J → ⟨ A ⟩
  β (i , p) = pr₁ (pr₂ (α i)) p

 {- the sup is defined only if some element is -}
 lift-sup-defined : pr₁ s → ∥ J ∥
 lift-sup-defined p = p

 {- the value of the sup is the sup of the values -}
 lift-sup-value : (p : pr₁ s) → is-sup (underlying-order A) (pr₁ (pr₂ s) p) β
 lift-sup-value p = ub , lub
  where
   ub : (j : J) → β j ⊑⟨ A ⟩ pr₁ (pr₂ s) p
   ub (i , pᵢ) = transport (λ - → β (i , pᵢ) ⊑⟨ A ⟩ -)
                   (value-is-constant s (pr₁ (∐-is-upperbound (𝓛ᵈ A) {I} {α} δ i) pᵢ) p)
                   (pr₂ (∐-is-upperbound (𝓛ᵈ A) {I} {α} δ i) pᵢ)
   lub : (u : ⟨ A ⟩) → ((j : J) → β j ⊑⟨ A ⟩ u) → pr₁ (pr₂ s) p ⊑⟨ A ⟩ u
   lub u h = pr₂ below p
    where
     u' : ⟨ 𝓛ᵈ A ⟩
     u' = pr₁ s , (λ _ → u) , being-defined-is-prop s
     below : s ⊑⟨ 𝓛ᵈ A ⟩ u'
     below = ∐-is-lowerbound-of-upperbounds (𝓛ᵈ A) {I} {α} δ u'
               (λ i → (λ pᵢ → pr₁ (∐-is-upperbound (𝓛ᵈ A) {I} {α} δ i) pᵢ) , (λ pᵢ → h (i , pᵢ)))

 {- the values of the defined elements are directed, when one is -}
 lift-values-directed : ∥ J ∥ → is-Directed A β
 lift-values-directed q = q , semi
  where
   semi : is-semidirected (underlying-order A) β
   semi (i , pᵢ) (j , pⱼ) = ∥∥-functor step (semidirected-if-Directed (𝓛ᵈ A) α δ i j)
    where
     step : (Σ k ꞉ I , (α i ⊑⟨ 𝓛ᵈ A ⟩ α k) × (α j ⊑⟨ 𝓛ᵈ A ⟩ α k))
          → Σ m ꞉ J , (β (i , pᵢ) ⊑⟨ A ⟩ β m) × (β (j , pⱼ) ⊑⟨ A ⟩ β m)
     step (k , (f , g) , (f' , g')) =
      (k , f pᵢ) , g pᵢ ,
      transport (λ - → β (j , pⱼ) ⊑⟨ A ⟩ pr₁ (pr₂ (α k)) -) (being-defined-is-prop (α k) (f' pⱼ) (f pᵢ)) (g' pⱼ)

 {- so a property closed under directed sups in A holds of the value of
    the sup when it holds of the values of the elements -}
 lift-sup-ind : {𝓦 : Universe} (Q : ⟨ A ⟩ → 𝓦 ̇ )
   → ({K : 𝓤₀ ̇ } (γ : K → ⟨ A ⟩) (ε : is-Directed A γ) → ((k : K) → Q (γ k)) → Q (∐ A ε))
   → ((i : I) (p : pr₁ (α i)) → Q (pr₁ (pr₂ (α i)) p))
   → (p : pr₁ s) → Q (pr₁ (pr₂ s) p)
 lift-sup-ind Q Q-sup h p =
  transport Q (sups-are-unique (underlying-order A) (pr₁ (axioms-of-dcpo A)) β
                 (∐-is-sup A (lift-values-directed p)) (lift-sup-value p))
    (Q-sup β (lift-values-directed p) (λ j → h (pr₁ j) (pr₂ j)))
