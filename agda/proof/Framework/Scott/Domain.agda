{-

  Scott domains: roll and unroll are inverse (from the solver), so values
  made with inj are defined.

-}

open import MLTT.Spartan
open import UF.FunExt
open import UF.PropTrunc
open import UF.Subsingletons

module proof.Framework.Scott.Domain
        (pt : propositional-truncations-exist)
        (fe : Fun-Ext)
        (pe : propext 𝓤₀)
       where

open import Framework.Scott.Base pt fe
open import Framework.Scott.Lift pt fe pe
open import Framework.Scott.Functor pt fe pe
open import Framework.Scott.Domain pt fe pe public
open import proof.Framework.Scott.Solve pt fe pe

private
 module I = SolutionIso (Liftᶠ Val) (Liftᶠ-⊥ Val) (Liftᶠ-strict Val)

unroll-roll : (l : ⟨ 𝓛ᵈ (obj Val 𝔻) ⟩) → unroll · (roll · l) ＝ l
unroll-roll = I.unfold-fold

roll-unroll : (d : ⟨ 𝔻 ⟩) → roll · (unroll · d) ＝ d
roll-unroll = I.fold-unfold

defined-inj : (t : Tag) (x : ⟨ obj (Payload t) 𝔻 ⟩) → defined (inj t · x)
defined-inj t x = transport is-defined (unroll-roll (η (t , x)) ⁻¹) ⋆
