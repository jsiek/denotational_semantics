{-

  Scott domains: lemmas about the operators. seq d e is e when d is
  defined, and depends on e only when d is defined; so strict functions,
  and function values Λ g, are equal when they agree on defined values;
  and guard n ds e is e when the ds are all defined.

-}

open import MLTT.Spartan hiding (inl; inr; cases)
open import UF.FunExt
open import UF.PropTrunc
open import UF.Subsingletons

open import Data.Fin using (Fin; zero; suc)

module proof.Framework.Scott.Ops
        (pt : propositional-truncations-exist)
        (fe : Fun-Ext)
        (pe : propext 𝓤₀)
       where

open import Framework.Scott.Base pt fe
open import Framework.Scott.Lift pt fe pe
open import proof.Framework.Scott.Domain pt fe pe public
open import Framework.Scott.Ops pt fe pe public

seq-defined : (d e : ⟨ 𝔻 ⟩) → defined d → seq · d · e ＝ e
seq-defined d e p = ∐ˢˢ-＝-if-domain-holds 𝔻⊥ (being-defined-is-prop (unroll · d)) p

seq-cong : (d e e' : ⟨ 𝔻 ⟩) → (defined d → e ＝ e') → seq · d · e ＝ seq · d · e'
seq-cong d e e' h = antisymmetry 𝔻 (guarded d e) (guarded d e') (below e e' h) (below e' e (λ p → h p ⁻¹))
 where
  ρ = being-defined-is-prop (unroll · d)
  below : (x y : ⟨ 𝔻 ⟩) → (defined d → x ＝ y) → guarded d x ⊑⟨ 𝔻 ⟩ guarded d y
  below x y k = ∐ˢˢ-is-lowerbound-of-upperbounds 𝔻⊥ (λ _ → x) ρ (guarded d y)
                  (λ p → transport (λ - → - ⊑⟨ 𝔻 ⟩ guarded d y) (k p ⁻¹)
                           (∐ˢˢ-is-upperbound 𝔻⊥ (λ _ → y) ρ p))

strict-cong : (g g' : DCPO[ 𝔻 , 𝔻 ]) → ((d : ⟨ 𝔻 ⟩) → defined d → g · d ＝ g' · d)
  → strict · g ＝ strict · g'
strict-cong g g' h = to-continuous-function-＝ 𝔻 𝔻 (λ d → seq-cong d (g · d) (g' · d) (h d))

Λ-cong : (g g' : DCPO[ 𝔻 , 𝔻 ]) → ((d : ⟨ 𝔻 ⟩) → defined d → g · d ＝ g' · d)
  → Λ · g ＝ Λ · g'
Λ-cong g g' h = ap (λ - → inj fun · -) (strict-cong g g' h)

guard-defined : (n : ℕ) (ds : Fin n → ⟨ 𝔻 ⟩) → ((i : Fin n) → defined (ds i))
  → (e : ⟨ 𝔻 ⟩) → guard n · ds · e ＝ e
guard-defined zero ds h e = refl
guard-defined (succ n) ds h e =
 seq-defined (ds zero) _ (h zero) ∙ guard-defined n (λ i → ds (suc i)) (λ i → h (suc i)) e
