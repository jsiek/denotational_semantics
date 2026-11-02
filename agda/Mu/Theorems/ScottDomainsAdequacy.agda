{-

  The adequacy of the Scott-domain semantics for the clocked
  interpreters of FPC and X86μ: the analogue, in Scott domains, of
  Theorem 4.5 (adequacy) of the paper (Mu/Theorems/Adequacy.agda, for
  the graph model), and the consequence drawn from it with compiler
  correctness in Scott domains (Mu/Theorems/ScottDomains.agda), the
  theorem the operational proofs state. The proofs are in
  Mu/proof/Adequacy/ScottDomains/. The X86μ statements are for the
  programs the compiler produces, so that their precondition (in
  Mu/proof/) need not be audited.

  A term means an element of the domain of values 𝔻
  (Framework/Scott/Domain.agda); const B c is the constant c() and ⊥𝔻
  means divergence. As in Mu/Theorems/ScottDomains.agda, the theorems
  are stated under the assumptions of TypeTopology's domain theory
  (propositional truncations, function extensionality and propositional
  extensionality), the parameters of this module.

  To read them: those of Mu/Theorems/ScottDomains.agda, the FPC
  interpreter (Mu/Semantics/ClockedInterpreters/FPC.agda), the X86μ
  interpreter (Mu/Semantics/ClockedInterpreters/X86.agda), the clocked
  semantics (Semantics/Interp/Clock.agda) and the observations
  (Semantics/Observation.agda).

-}

open import MLTT.Spartan using (𝓤₀; _×_; _＝_)
open import UF.FunExt using (Fun-Ext)
open import UF.PropTrunc using (propositional-truncations-exist)
open import UF.Subsingletons using (propext)

open import Framework.Primitives using (Base; base-rep; Int)
open import Mu.Language.Type using (base)
open import Mu.Compiler.Pipeline using (compile)
open import Semantics.Observation using (o-const; _⇔_)
open import Semantics.Interp.Clock using (Terminates; Diverges)
import Mu.Language.FPC as FPC
import Mu.Semantics.ClockedInterpreters.FPC as FPCᵢ
import Mu.Semantics.ClockedInterpreters.X86 as X86μᵢ

open import Data.List using ([])
open import Data.Integer using (ℤ)

module Mu.Theorems.ScottDomainsAdequacy
        (pt : propositional-truncations-exist)
        (fe : Fun-Ext)
        (pe : propext 𝓤₀)
       where

open import Framework.Scott.Base pt fe using (_·_)
open import Framework.Scott.Ops pt fe pe using (const; ⊥𝔻)
open import Mu.Semantics.ScottDomains.FPC pt fe pe using (⟦_⟧)
open import Mu.Semantics.ScottDomains.Closed pt fe pe using (ρ₀)
open import Mu.Semantics.ScottDomains.X86 pt fe pe using (⟦_⟧ₜ)

import Mu.proof.Adequacy.ScottDomains.FPC pt fe pe as AdequacyFPC
import Mu.proof.Adequacy.ScottDomains.X86 pt fe pe as AdequacyX86
import Mu.proof.Adequacy.ScottDomains.EndToEnd pt fe pe as EndToEnd

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

{- the same holds for X86μ and compile M -}

x86-const-iff : ∀ {A} (M : FPC.Tm [] A) (B : Base) (c : base-rep B)
  → (⟦ compile M ⟧ₜ ＝ const B c → Terminates (X86μᵢ.sem (compile M)) (o-const B c))
  × (Terminates (X86μᵢ.sem (compile M)) (o-const B c) → ⟦ compile M ⟧ₜ ＝ const B c)
x86-const-iff = AdequacyX86.x86-const-iff

x86-diverges-iff : ∀ {A} (M : FPC.Tm [] A)
  → (Diverges (X86μᵢ.sem (compile M)) → ⟦ compile M ⟧ₜ ＝ ⊥𝔻)
  × (⟦ compile M ⟧ₜ ＝ ⊥𝔻 → Diverges (X86μᵢ.sem (compile M)))
x86-diverges-iff = AdequacyX86.x86-diverges-iff

{- With compiler correctness (Mu/Theorems/ScottDomains.agda): the compiler,
   observed through the interpreters ----------------------------------------}

{- for a program of type Int, the theorem the operational proofs state:
   the interpreters of FPC and X86μ terminate with the same integer, or
   both diverge -}

end-to-end-x86-const : ∀ (M : FPC.Tm [] (base Int)) (n : ℤ)
  → Terminates (FPCᵢ.sem M) (o-const Int n) ⇔ Terminates (X86μᵢ.sem (compile M)) (o-const Int n)
end-to-end-x86-const = EndToEnd.compile-const

end-to-end-x86-diverges : ∀ (M : FPC.Tm [] (base Int))
  → Diverges (FPCᵢ.sem M) ⇔ Diverges (X86μᵢ.sem (compile M))
end-to-end-x86-diverges = EndToEnd.compile-diverges
