{-

  Scott domains: lifting. 𝓛ᵈ A is TypeTopology's lifting of a dcpo A
  (freely adding a least element): its elements are partial elements
  (P , φ), a proposition P (in 𝓤₀) and φ : P → ⟨ A ⟩. The action of
  lifting on a continuous map, 𝓛map m (P , φ) = (P , m ∘ φ), is
  continuous, and continuous in m. The extension of a continuous map
  into a pointed dcpo to a strict one on 𝓛ᵈ A is TypeTopology's f̃.

  Lifting uses propositional extensionality (pe), for propositions in 𝓤₀.

-}

open import MLTT.Spartan hiding (J)
open import UF.FunExt
open import UF.PropTrunc
open import UF.Subsingletons

module Framework.Scott.Lift
        (pt : propositional-truncations-exist)
        (fe : Fun-Ext)
        (pe : propext 𝓤₀)
       where

open import Framework.Scott.Base pt fe
open import Lifting.Construction 𝓤₀ using (𝓛; η; is-defined; value; being-defined-is-prop) public
open import Lifting.Miscelanea 𝓤₀ using (value-is-constant)
open import DomainTheory.Lifting.LiftingDcpo pt fe 𝓤₀ pe
open import DomainTheory.Lifting.LiftingSet pt fe 𝓤₀ pe using (module lifting-is-free-pointed-dcpo-on-set)

𝓛ᵈ : DCPO₁ → DCPO₁
𝓛ᵈ A = freely-add-⊥.𝓛-DCPO A

𝓛ᵈ⊥ : DCPO₁ → DCPO⊥ {𝓤₁} {𝓤₁}
𝓛ᵈ⊥ A = freely-add-⊥.𝓛-DCPO⊥ A

ηᶜ : (A : DCPO₁) → DCPO[ A , 𝓛ᵈ A ]
ηᶜ A = η , freely-add-⊥.η-is-continuous A

{- the strict extension of a continuous map into a pointed dcpo -}
module _ (A : DCPO₁) {𝓤' 𝓣' : Universe} (E : DCPO⊥ {𝓤'} {𝓣'}) (f : DCPO[ A , E ⁻ ]) where

 extend : DCPO[ 𝓛ᵈ A , E ⁻ ]
 extend = lifting-is-free-pointed-dcpo-on-set.f̃ (sethood A) E (pr₁ f) , freely-add-⊥.f̃-is-continuous' A E (pr₁ f) (pr₂ f)

 extend-η : (x : ⟨ A ⟩) → extend · η x ＝ f · x
 extend-η = freely-add-⊥.f̃-after-η-is-f' A E (pr₁ f) (pr₂ f)

 extend-⊥ : extend · ⊥ (𝓛ᵈ⊥ A) ＝ ⊥ E
 extend-⊥ = freely-add-⊥.f̃-is-strict' A E (pr₁ f) (pr₂ f)

{- the action on maps -}
module _ (A B : DCPO₁) where

 𝓛map : DCPO[ A , B ] → ⟨ 𝓛ᵈ A ⟩ → ⟨ 𝓛ᵈ B ⟩
 𝓛map m (P , φ , i) = P , (λ p → m · φ p) , i

 𝓛map-is-continuous : (m : DCPO[ A , B ]) → is-continuous (𝓛ᵈ A) (𝓛ᵈ B) (𝓛map m)
 𝓛map-is-continuous m I α δ = ub , lub
  where
   J : 𝓤₀ ̇
   J = Σ i ꞉ I , is-defined (α i)
   β : J → ⟨ A ⟩
   β (i , p) = value (α i) p
   ε : ∥ J ∥ → is-Directed A β
   ε = freely-add-⊥.family-in-dcpo-is-directed A α δ
   m-mono = monotone-if-continuous A B m
   ub : (i : I) → 𝓛map m (α i) ⊑⟨ 𝓛ᵈ B ⟩ 𝓛map m (∐ (𝓛ᵈ A) {I} {α} δ)
   ub i = (λ p → ∣ i , p ∣) , (λ p → m-mono (value (α i) p) (∐ A (ε ∣ i , p ∣)) (∐-is-upperbound A (ε ∣ i , p ∣) (i , p)))
   lub : (l : ⟨ 𝓛ᵈ B ⟩) → ((i : I) → 𝓛map m (α i) ⊑⟨ 𝓛ᵈ B ⟩ l)
       → 𝓛map m (∐ (𝓛ᵈ A) {I} {α} δ) ⊑⟨ 𝓛ᵈ B ⟩ l
   lub l u = g , r
    where
     g : ∥ J ∥ → is-defined l
     g = ∥∥-rec (being-defined-is-prop l) (λ (i , p) → pr₁ (u i) p)
     r : (q : ∥ J ∥) → m · ∐ A (ε q) ⊑⟨ B ⟩ value l (g q)
     r q = sup-is-lowerbound-of-upperbounds (underlying-order B) (pr₂ m _ β (ε q))
            (value l (g q))
            (λ (i , p) → transitivity B (m · value (α i) p) _ _ (pr₂ (u i) p)
                           (＝-to-⊑ B (value-is-constant l (pr₁ (u i) p) (g q))))

 𝓛mapᵈ : DCPO[ A , B ] → DCPO[ 𝓛ᵈ A , 𝓛ᵈ B ]
 𝓛mapᵈ m = 𝓛map m , 𝓛map-is-continuous m

 𝓛map-is-continuous-in-map : (l : ⟨ 𝓛ᵈ A ⟩) → is-continuous (A ⟹₁ B) (𝓛ᵈ B) (λ m → 𝓛map m l)
 𝓛map-is-continuous-in-map (P , φ , i) I α δ = ub , lub
  where
   ε : (p : P) → is-Directed B (λ j → α j · φ p)
   ε p = pointwise-directed A B α δ (φ p)
   ub : (j : I) → 𝓛map (α j) (P , φ , i) ⊑⟨ 𝓛ᵈ B ⟩ 𝓛map (∐ (A ⟹₁ B) {I} {α} δ) (P , φ , i)
   ub j = id , (λ p → ∐-is-upperbound B (ε p) j)
   lub : (l : ⟨ 𝓛ᵈ B ⟩) → ((j : I) → 𝓛map (α j) (P , φ , i) ⊑⟨ 𝓛ᵈ B ⟩ l)
       → 𝓛map (∐ (A ⟹₁ B) {I} {α} δ) (P , φ , i) ⊑⟨ 𝓛ᵈ B ⟩ l
   lub l u = g , r
    where
     g : P → is-defined l
     g p = ∥∥-rec (being-defined-is-prop l) (λ j → pr₁ (u j) p) (inhabited-if-Directed (A ⟹₁ B) α δ)
     r : (p : P) → ∐ B (ε p) ⊑⟨ B ⟩ value l (g p)
     r p = ∐-is-lowerbound-of-upperbounds B (ε p) (value l (g p))
            (λ j → transitivity B _ _ _ (pr₂ (u j) p)
                     (＝-to-⊑ B (value-is-constant l (pr₁ (u j) p) (g p))))

 𝓛mapᶜ : DCPO[ A ⟹₁ B , 𝓛ᵈ A ⟹₁ 𝓛ᵈ B ]
 𝓛mapᶜ = to-exp₁ (A ⟹₁ B) (𝓛ᵈ A) (𝓛ᵈ B) 𝓛mapᵈ 𝓛map-is-continuous-in-map
