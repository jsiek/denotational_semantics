{-

  Scott domains: the domain of values, the solution of

    𝔻 ≅ 𝓛 ( Σ t : Tag , Payload t 𝔻 )

  where a tag is a constant, a tuple of n components (𝔻ⁿ), left or right
  (𝔻), a function (𝔻 ⟹ 𝔻) or a pair (𝔻², the closures of Clos4μ and
  later): as the graph model's values (Framework/GraphModel/Domain.agda),
  without its error value, as ISWIMμ has no errors. The least element
  of 𝔻 means no value (divergence).

  A value is made with inj t, and taken apart, strictly, by case: case h
  maps inj t x to h t x and ⊥ to ⊥.

-}

open import MLTT.Spartan
open import UF.FunExt
open import UF.PropTrunc
open import UF.Subsingletons
open import UF.Sets

open import Framework.Primitives using (Base; base-rep)
open import Data.Fin using (Fin)

module Framework.Scott.Domain
        (pt : propositional-truncations-exist)
        (fe : Fun-Ext)
        (pe : propext 𝓤₀)
       where

open import Framework.Scott.Base pt fe
open import Framework.Scott.Sum pt fe
open import Framework.Scott.Lift pt fe pe
open import Framework.Scott.Functor pt fe pe
open import Framework.Scott.Solve pt fe pe

data Tag : 𝓤₀ ̇ where
  con : (B : Base) → base-rep B → Tag   {- a constant -}
  tup : ℕ → Tag                         {- a tuple of n components -}
  left : Tag                            {- sums -}
  right : Tag
  fun : Tag                             {- a function -}
  pr : Tag                              {- a pair -}

{- every type is a set, as this development uses K -}
Tag-is-set : is-set Tag
Tag-is-set refl refl = refl

Payload : Tag → Functor
Payload (con B k) = Constᶠ 𝟙ᵈ
Payload (tup n) = Powᶠ (Fin n) Idᶠ
Payload left = Idᶠ
Payload right = Idᶠ
Payload fun = Expᶠ Idᶠ Idᶠ
Payload pr = Powᶠ (Fin 2) Idᶠ

Val : Functor
Val = Σᶠ Tag Tag-is-set Payload

module 𝔻-solution = Solution (Liftᶠ Val) (Liftᶠ-⊥ Val) (Liftᶠ-strict Val)
open 𝔻-solution using (D∞-has-least)
  renaming (D∞ to 𝔻; fold to roll; unfold to unroll) public

𝔻⊥ : DCPO⊥ {𝓤₁} {𝓤₁}
𝔻⊥ = 𝔻 , D∞-has-least

{- a value with a given tag -}
inj : (t : Tag) → DCPO[ obj (Payload t) 𝔻 , 𝔻 ]
inj t = ∘₁ (obj (Payload t) 𝔻) (𝓛ᵈ (obj Val 𝔻)) 𝔻
          (∘₁ (obj (Payload t) 𝔻) (obj Val 𝔻) (𝓛ᵈ (obj Val 𝔻))
             (ι Tag Tag-is-set (λ t → obj (Payload t) 𝔻) t) (ηᶜ (obj Val 𝔻)))
          roll

{- taking a value apart, strictly -}
case : (E : DCPO⊥ {𝓤₁} {𝓤₁}) → ((t : Tag) → DCPO[ obj (Payload t) 𝔻 , E ⁻ ]) → DCPO[ 𝔻 , E ⁻ ]
case E h = ∘₁ 𝔻 (𝓛ᵈ (obj Val 𝔻)) (E ⁻) unroll
             (extend (obj Val 𝔻) E (copair Tag Tag-is-set (λ t → obj (Payload t) 𝔻) (E ⁻) h))

{- a value is defined when it is not ⊥ -}
defined : ⟨ 𝔻 ⟩ → 𝓤₀ ̇
defined d = is-defined (unroll · d)
