{-

  The adequacy of the Scott-domain semantics for the clocked
  interpreters of FPC and X86μ: the analogue, in Scott domains, of
  Theorem 4.5 (adequacy) of the paper (Mu/Theorems/Adequacy.agda, for
  the graph model). The proofs are in Mu/proof/Adequacy/ScottDomains/.

  A term means an element of the domain of values 𝔻
  (Framework/Scott/Domain.agda); const B c is the constant c() and ⊥𝔻
  means divergence. As in Mu/Theorems/ScottDomains.agda, the theorems
  are stated under the assumptions of TypeTopology's domain theory
  (propositional truncations, function extensionality and propositional
  extensionality), the parameters of this module.

  To read them: those of Mu/Theorems/ScottDomains.agda, the FPC
  interpreter (Mu/Semantics/ClockedInterpreters/FPC.agda), the clocked
  semantics (Semantics/Interp/Clock.agda) and the observations
  (Semantics/Observation.agda).

-}

open import MLTT.Spartan using (𝓤₀; _×_; _＝_)
open import UF.FunExt using (Fun-Ext)
open import UF.PropTrunc using (propositional-truncations-exist)
open import UF.Subsingletons using (propext)

open import Framework.Primitives using (Base; base-rep)
open import Semantics.Observation using (o-const)
open import Semantics.Interp.Clock using (Terminates; Diverges)
import Mu.Language.FPC as FPC
import Mu.Semantics.ClockedInterpreters.FPC as FPCᵢ

open import Data.List using ([])

module Mu.Theorems.ScottDomainsAdequacy
        (pt : propositional-truncations-exist)
        (fe : Fun-Ext)
        (pe : propext 𝓤₀)
       where

open import Framework.Scott.Base pt fe using (_·_)
open import Framework.Scott.Ops pt fe pe using (const; ⊥𝔻)
open import Mu.Semantics.ScottDomains.FPC pt fe pe using (⟦_⟧)
open import Mu.Semantics.ScottDomains.Closed pt fe pe using (ρ₀)

import Mu.proof.Adequacy.ScottDomains.FPC pt fe pe as AdequacyFPC

{- Adequacy, Scott domains -----------------------------------------------------}

{- for a closed FPC term M (of any type), and every constant c:
   ⟦ M ⟧ ρ₀ = c() if and only if the interpreter of FPC terminates on M
   with c -}
fpc-const-iff : ∀ {A} (M : FPC.Tm [] A) (B : Base) (c : base-rep B)
  → (⟦ M ⟧ · ρ₀ ＝ const B c → Terminates (FPCᵢ.sem M) (o-const B c))
  × (Terminates (FPCᵢ.sem M) (o-const B c) → ⟦ M ⟧ · ρ₀ ＝ const B c)
fpc-const-iff = AdequacyFPC.const-iff

{- and ⟦ M ⟧ ρ₀ is ⊥ if and only if the interpreter diverges on M -}
fpc-diverges-iff : ∀ {A} (M : FPC.Tm [] A)
  → (Diverges (FPCᵢ.sem M) → ⟦ M ⟧ · ρ₀ ＝ ⊥𝔻)
  × (⟦ M ⟧ · ρ₀ ＝ ⊥𝔻 → Diverges (FPCᵢ.sem M))
fpc-diverges-iff = AdequacyFPC.diverges-iff
