{-

  The correctness of the compiler in Scott domains (a pilot: the enclose
  pass only): the public statements. The proofs are in
  proof/Correctness/Scott/; each theorem here is one of them, with its
  type written out, so that it can be read without opening proof/.

  The domain theory is Tom de Jong's, in TypeTopology, which assumes
  propositional truncations, function extensionality and propositional
  extensionality; so these theorems are stated, and hold, under those
  assumptions, which are the parameters of this module (they are
  consistent with the axiom K that this development uses).

  To read them: the languages (Language/), the passes (Compiler/), the
  semantics of ISWIM and Clos2 (Semantics/Scott/), and the domain, its
  operators and the semantics of any signature (Framework/Scott/).

-}

open import MLTT.Spartan
open import UF.FunExt
open import UF.PropTrunc
open import UF.Subsingletons

import Language.ISWIM as ISWIM
open import Compiler.Enclose using (enclose)

module Theorems.Scott
        (pt : propositional-truncations-exist)
        (fe : Fun-Ext)
        (pe : propext 𝓤₀)
       where

open import Framework.Scott.Base pt fe using (_·_; ⟨_⟩)
open import Framework.Scott.Lift pt fe pe using (𝓛ᵈ)
open import Framework.Scott.Functor pt fe pe using (obj)
open import Framework.Scott.Domain pt fe pe using (𝔻; Val; roll; unroll)
open import Framework.Scott.Ops pt fe pe using (Env; ω)
open import Semantics.Scott.ISWIM pt fe pe using (⟦_⟧)
open import Semantics.Scott.Clos2 pt fe pe using () renaming (⟦_⟧ to ⟦_⟧₂)

import proof.Framework.Scott.Domain pt fe pe as Domain
import proof.Correctness.Scott.EncloseCorrect pt fe pe as EncloseCorrect

{- The domain of values solves its equation: 𝔻 ≅ 𝓛 (Σ t , Payload t 𝔻) -}

unroll-roll : (l : ⟨ 𝓛ᵈ (obj Val 𝔻) ⟩) → unroll · (roll · l) ＝ l
unroll-roll = Domain.unroll-roll

roll-unroll : (d : ⟨ 𝔻 ⟩) → roll · (unroll · d) ＝ d
roll-unroll = Domain.roll-unroll

{- The environment of a closed program: every variable means ω, the error
   value. (It only matters for open terms, as the passes are stated on
   whole terms.) -}
ρ₀ : ⟨ Env ⟩
ρ₀ = λ _ → ω

{- enclose preserves the meaning of a program exactly -}
enclose-correct : (M : ISWIM.AST) → ⟦ M ⟧ · ρ₀ ＝ ⟦ enclose M ⟧₂ · ρ₀
enclose-correct = EncloseCorrect.enclose-correct-closed
