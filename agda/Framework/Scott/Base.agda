{-

  Scott domains: the basics, on top of Tom de Jong's domain theory in
  TypeTopology (DomainTheory.*): the dcpos of this development (DCPO₁:
  carrier and order in 𝓤₁, directed families indexed by types in 𝓤₀),
  applying a continuous map, the identity and composition, continuity
  into an exponential (pointwise), the one-point dcpo, and powers Aᴵ of a
  dcpo (pointwise order; used for tuples and environments).

  Everything is parameterised by propositional truncation (pt) and
  function extensionality (fe), which TypeTopology takes as assumptions.

-}

open import MLTT.Spartan
open import UF.FunExt
open import UF.PropTrunc
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import UF.Sets
open import UF.Sets-Properties
open import UF.Subsingletons-Properties

module Framework.Scott.Base
        (pt : propositional-truncations-exist)
        (fe : Fun-Ext)
       where

open PropositionalTruncation pt public
open import DomainTheory.Basics.Dcpo pt fe 𝓤₀ public
open import DomainTheory.Basics.Miscelanea pt fe 𝓤₀ public
open import DomainTheory.Basics.Pointed pt fe 𝓤₀ public
open import DomainTheory.Basics.Exponential pt fe 𝓤₀ public
open import DomainTheory.Basics.Products pt fe public
open DcpoProductsGeneral 𝓤₀ public
open import DomainTheory.Basics.ProductsContinuity pt fe 𝓤₀ public
open import DomainTheory.Basics.Curry pt fe 𝓤₀ public

{- the dcpos of this development -}
DCPO₁ : 𝓤₂ ̇
DCPO₁ = DCPO {𝓤₁} {𝓤₁}

{- applying a continuous map -}
infixl 30 _·_
_·_ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {P : (X → Y) → 𝓦 ̇ } → Σ P → X → Y
f · x = pr₁ f x

idᶜ : (A : DCPO {𝓤} {𝓣}) → DCPO[ A , A ]
idᶜ A = id , id-is-continuous A

{- identity and composition (g ∘ f) at DCPO₁, with their universe levels
   fixed: Agda compares two applications of DCPO-∘ whose levels are
   written differently by unfolding them, which can take very long -}
id₁ : (A : DCPO₁) → DCPO[ A , A ]
id₁ A = idᶜ A

∘₁ : (A B C : DCPO₁) → DCPO[ A , B ] → DCPO[ B , C ] → DCPO[ A , C ]
∘₁ A B C f g = DCPO-∘ A B C f g

{- a map into an exponential is continuous if it is pointwise -}
to-exp-continuous : {𝓤' 𝓣' 𝓦 𝓦' : Universe}
  → (A : DCPO {𝓤} {𝓣}) (B : DCPO {𝓤'} {𝓣'}) (C : DCPO {𝓦} {𝓦'})
  → (f : ⟨ A ⟩ → DCPO[ B , C ])
  → ((b : ⟨ B ⟩) → is-continuous A C (λ a → f a · b))
  → is-continuous A (B ⟹ᵈᶜᵖᵒ C) f
to-exp-continuous A B C f c I α δ = ub , lub
 where
  ub : (i : I) → f (α i) ⊑⟨ B ⟹ᵈᶜᵖᵒ C ⟩ f (∐ A δ)
  ub i b = sup-is-upperbound (underlying-order C) (c b I α δ) i
  lub : (g : ⟨ B ⟹ᵈᶜᵖᵒ C ⟩) → ((i : I) → f (α i) ⊑⟨ B ⟹ᵈᶜᵖᵒ C ⟩ g)
      → f (∐ A δ) ⊑⟨ B ⟹ᵈᶜᵖᵒ C ⟩ g
  lub g u b = sup-is-lowerbound-of-upperbounds (underlying-order C) (c b I α δ)
               (g · b) (λ i → u i b)

{- pairing, and evaluation at a point -}
pairᶜ : {𝓤' 𝓣' 𝓦 𝓦' : Universe}
  → (P : DCPO {𝓤} {𝓣}) (X : DCPO {𝓤'} {𝓣'}) (Y : DCPO {𝓦} {𝓦'})
  → DCPO[ P , X ] → DCPO[ P , Y ] → DCPO[ P , X ×ᵈᶜᵖᵒ Y ]
pairᶜ P X Y f g = (λ p → f · p , g · p) , c
 where
  c : is-continuous P (X ×ᵈᶜᵖᵒ Y) (λ p → f · p , g · p)
  c I α δ = (λ i → sup-is-upperbound (underlying-order X) (pr₂ f I α δ) i ,
                   sup-is-upperbound (underlying-order Y) (pr₂ g I α δ) i) ,
            (λ (x , y) u → sup-is-lowerbound-of-upperbounds (underlying-order X) (pr₂ f I α δ) x (λ i → pr₁ (u i)) ,
                           sup-is-lowerbound-of-upperbounds (underlying-order Y) (pr₂ g I α δ) y (λ i → pr₂ (u i)))

at-point : {𝓤' 𝓣' : Universe} (X : DCPO {𝓤} {𝓣}) (Y : DCPO {𝓤'} {𝓣'})
  → ⟨ X ⟩ → DCPO[ X ⟹ᵈᶜᵖᵒ Y , Y ]
at-point X Y x = (λ f → f · x) , c
 where
  c : is-continuous (X ⟹ᵈᶜᵖᵒ Y) Y (λ f → f · x)
  c I α δ = ∐-is-sup Y (pointwise-family-is-directed X Y α δ x)

{- the one-point dcpo -}
𝟙ᵈ : DCPO₁
𝟙ᵈ = 𝟙 , (λ _ _ → 𝟙) , (props-are-sets 𝟙-is-prop , (λ _ _ → 𝟙-is-prop)
     , (λ _ → ⋆) , (λ _ _ _ _ _ → ⋆) , (λ _ _ _ _ → 𝟙-is-prop _ _))
     , (λ I α δ → ⋆ , (λ _ → ⋆) , (λ _ _ → ⋆))

{- Powers ---------------------------------------------------------------------}

module _ (I : 𝓤₀ ̇ ) (A : DCPO₁) where

 private
  _⊑ᴾ_ : (I → ⟨ A ⟩) → (I → ⟨ A ⟩) → 𝓤₁ ̇
  f ⊑ᴾ g = (i : I) → f i ⊑⟨ A ⟩ g i

 component-is-directed : {J : 𝓤₀ ̇ } (α : J → I → ⟨ A ⟩) → is-directed _⊑ᴾ_ α
   → (i : I) → is-Directed A (λ j → α j i)
 component-is-directed α δ i =
  inhabited-if-directed _⊑ᴾ_ α δ ,
  (λ j k → ∥∥-functor (λ (l , u , v) → l , u i , v i)
                      (semidirected-if-directed _⊑ᴾ_ α δ j k))

 Pow : DCPO₁
 Pow = (I → ⟨ A ⟩) , _⊑ᴾ_
     , (Π-is-set fe (λ _ → sethood A)
     , (λ f g → Π-is-prop fe (λ i → prop-valuedness A (f i) (g i)))
     , (λ f i → reflexivity A (f i))
     , (λ f g h u v i → transitivity A (f i) (g i) (h i) (u i) (v i))
     , (λ f g u v → dfunext fe (λ i → antisymmetry A (f i) (g i) (u i) (v i))))
     , (λ J α δ → (λ i → ∐ A (component-is-directed α δ i))
                , (λ j i → ∐-is-upperbound A (component-is-directed α δ i) j)
                , (λ g u i → ∐-is-lowerbound-of-upperbounds A
                               (component-is-directed α δ i) (g i) (λ j → u j i)))

 {- a map into a power is continuous if each component is -}
 to-Pow-continuous : (B : DCPO {𝓤} {𝓣}) (f : ⟨ B ⟩ → I → ⟨ A ⟩)
   → ((i : I) → is-continuous B A (λ b → f b i))
   → is-continuous B Pow f
 to-Pow-continuous B f c J α δ =
  (λ j i → sup-is-upperbound (underlying-order A) (c i J α δ) j) ,
  (λ g u i → sup-is-lowerbound-of-upperbounds (underlying-order A) (c i J α δ)
                (g i) (λ j → u j i))

 {- a component of a power -}
 at : I → DCPO[ Pow , A ]
 at i = (λ f → f i) ,
        (λ J α δ → ∐-is-upperbound A (component-is-directed α δ i) ,
                   (λ a u → ∐-is-lowerbound-of-upperbounds A
                              (component-is-directed α δ i) a u))
