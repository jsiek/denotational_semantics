{-

  The correctness of the ISWIMμ compiler (Mu/Compiler/Pipeline.agda) in
  Scott domains: the public statements. The proofs are in
  Mu/proof/Correctness/Scott/; each theorem here is one of them, with
  its type written out, as Mu/Theorems/Denotational.agda does for the
  graph model.

    ISWIMμ --simplify--> ISWIMμ --enclose--> Clos2μ --optimize--> Clos2μ
           --concretize--> Clos3μ --delay--> Clos4μ --globalize--> Clos5μ
           --rco--> Monμ --lift locals--> Impμ --explicate control--> CFGμ
           --select instructions--> X86μ

  A term means an element of the domain of values 𝔻, a solution of
  𝔻 ≅ 𝓛 (Σ t , Payload t 𝔻) (Framework/Scott/Domain.agda), whose least
  element means divergence. The domain theory is Tom de Jong's, in
  TypeTopology, which assumes propositional truncations, function
  extensionality and propositional extensionality; so these theorems
  are stated, and hold, under those assumptions, which are the
  parameters of this module (consistent with the axiom K that this
  development uses).

  To read them: the languages (Mu/Language/), the passes
  (Mu/Compiler/), the semantics of each language, X86μ included
  (Mu/Semantics/Scott/; Monμ means its embedding into Clos5μ, ⌜_⌝ₚ),
  and the domain, its operators and the combinators the semantics are
  built with (Framework/Scott/).

-}

open import MLTT.Spartan using (𝓤₀; _×_; _＝_; pr₁; pr₂)
open import UF.FunExt using (Fun-Ext)
open import UF.PropTrunc using (propositional-truncations-exist)
open import UF.Subsingletons using (propext)

open import Framework.Primitives using (Base; base-rep; Int)
open import Mu.Language.Type using (base)
import Mu.Language.ISWIM as ISWIMμ
import Mu.Language.Clos2 as Clos2μ
import Mu.Language.Clos3 as Clos3μ
import Mu.Language.Clos4 as Clos4μ
import Mu.Language.Clos5 as Clos5μ
import Mu.Language.Mon as Monμ
open Monμ using (⌜_⌝ₚ)
import Mu.Language.Imp as Impμ
import Mu.Language.CFG as CFGμ

open import Mu.Compiler.Simplify using (simplify)
open import Mu.Compiler.Enclose using (enclose)
open import Mu.Compiler.Optimize using (optimize-program)
open import Mu.Compiler.Concretize using (concretize-program)
open import Mu.Compiler.Delay using (delay-program)
open import Mu.Compiler.Globalize using (globalize)
open import Mu.Compiler.RCO using (rco-program)
open import Mu.Compiler.LiftLocals using (lift-program)
open import Mu.Compiler.Explicate using (explicate)
open import Mu.Compiler.Select using (select)
open import Mu.Compiler.Pipeline using (compile; compile-mon; compile-imp; compile-cfg; compile-x86)

open import Data.List using ([])

module Mu.Theorems.Scott
        (pt : propositional-truncations-exist)
        (fe : Fun-Ext)
        (pe : propext 𝓤₀)
       where

open import Framework.Scott.Base pt fe using (_·_; ⟨_⟩)
open import Framework.Scott.Lift pt fe pe using (𝓛ᵈ)
open import Framework.Scott.Functor pt fe pe using (obj)
open import Framework.Scott.Domain pt fe pe using (𝔻; Val; roll; unroll; defined)
open import Framework.Scott.Ops pt fe pe using (const)

open import Mu.Semantics.Scott.ISWIM pt fe pe using (⟦_⟧)
open import Mu.Semantics.Scott.Clos2 pt fe pe using () renaming (⟦_⟧ to ⟦_⟧₂)
open import Mu.Semantics.Scott.Clos3 pt fe pe using () renaming (⟦_⟧ to ⟦_⟧₃)
open import Mu.Semantics.Scott.Clos4 pt fe pe using () renaming (⟦_⟧ to ⟦_⟧₄)
open import Mu.Semantics.Scott.Clos5 pt fe pe using () renaming (⟦_⟧ₚ to ⟦_⟧₅)
open import Mu.Semantics.Scott.Imp pt fe pe using () renaming (⟦_⟧ₚ to ⟦_⟧ᵢ)
open import Mu.Semantics.Scott.CFG pt fe pe using () renaming (⟦_⟧ₚ to ⟦_⟧ᶜ)
open import Mu.Semantics.Scott.X86 pt fe pe using (⟦_⟧ₜ)

import proof.Framework.Scott.Domain pt fe pe as Domain
import Mu.proof.Correctness.Scott.SimplifyCorrect pt fe pe as Simplify
import Mu.proof.Correctness.Scott.EncloseCorrect pt fe pe as Enclose
import Mu.proof.Correctness.Scott.OptimizeCorrect pt fe pe as Optimize
import Mu.proof.Correctness.Scott.ConcretizeCorrect pt fe pe as Concretize
import Mu.proof.Correctness.Scott.DelayCorrect pt fe pe as Delay
import Mu.proof.Correctness.Scott.GlobalizeCorrect pt fe pe as Globalize
import Mu.proof.Correctness.Scott.RCOCorrect pt fe pe as RCO
import Mu.proof.Correctness.Scott.LiftLocalsCorrect pt fe pe as LiftLocals
import Mu.proof.Correctness.Scott.ExplicateCorrect pt fe pe as Explicate
import Mu.proof.Correctness.Scott.SelectCorrect pt fe pe as Select
import Mu.proof.Correctness.Scott.CompilerCorrect pt fe pe as Compiler

{- The environment of a closed program: every variable means the empty
   tuple (Mu/Semantics/Scott/Closed.agda). -}
open import Mu.Semantics.Scott.Closed pt fe pe public using (ρ₀)

{- The domain of values solves its equation: 𝔻 ≅ 𝓛 (Σ t , Payload t 𝔻) -}

unroll-roll : (l : ⟨ 𝓛ᵈ (obj Val 𝔻) ⟩) → unroll · (roll · l) ＝ l
unroll-roll = Domain.unroll-roll

roll-unroll : (d : ⟨ 𝔻 ⟩) → roll · (unroll · d) ＝ d
roll-unroll = Domain.roll-unroll

{- Each pass ------------------------------------------------------------------}

{- every pass but delay preserves the meaning of a program exactly -}

simplify-correct : ∀ {A} (M : ISWIMμ.Tm [] A) → ⟦ M ⟧ · ρ₀ ＝ ⟦ simplify M ⟧ · ρ₀
simplify-correct = Simplify.simplify-correct

enclose-correct : ∀ {A} (M : ISWIMμ.Tm [] A) → ⟦ M ⟧ · ρ₀ ＝ ⟦ enclose M ⟧₂ · ρ₀
enclose-correct = Enclose.enclose-correct

optimize-correct : ∀ {A} (M : Clos2μ.Tm [] A) → ⟦ M ⟧₂ · ρ₀ ＝ ⟦ optimize-program M ⟧₂ · ρ₀
optimize-correct = Optimize.optimize-correct

concretize-correct : ∀ {A} (M : Clos2μ.Tm [] A) → ⟦ M ⟧₂ · ρ₀ ＝ ⟦ concretize-program M ⟧₃ · ρ₀
concretize-correct = Concretize.concretize-correct

{- delay preserves and reflects the constants a program produces, and
   whether it produces anything (whether its meaning is defined) -}
delay-correct-const : ∀ {A} (M : Clos3μ.Tm [] A) (B : Base) (c : base-rep B)
  → (⟦ M ⟧₃ · ρ₀ ＝ const B c → ⟦ delay-program M ⟧₄ · ρ₀ ＝ const B c)
  × (⟦ delay-program M ⟧₄ · ρ₀ ＝ const B c → ⟦ M ⟧₃ · ρ₀ ＝ const B c)
delay-correct-const = Delay.delay-correct-const

delay-correct-defined : ∀ {A} (M : Clos3μ.Tm [] A)
  → (defined (⟦ M ⟧₃ · ρ₀) → defined (⟦ delay-program M ⟧₄ · ρ₀))
  × (defined (⟦ delay-program M ⟧₄ · ρ₀) → defined (⟦ M ⟧₃ · ρ₀))
delay-correct-defined = Delay.delay-correct-defined

globalize-correct : ∀ {A} (M : Clos4μ.Tm [] A) → ⟦ M ⟧₄ · ρ₀ ＝ ⟦ globalize M ⟧₅
globalize-correct = Globalize.globalize-correct

rco-correct : ∀ {A} (P : Clos5μ.Program A) → ⟦ P ⟧₅ ＝ ⟦ ⌜ rco-program P ⌝ₚ ⟧₅
rco-correct = RCO.rco-correct

lift-locals-correct : ∀ {A} (P : Monμ.Program A) → ⟦ ⌜ P ⌝ₚ ⟧₅ ＝ ⟦ lift-program P ⟧ᵢ
lift-locals-correct = LiftLocals.lift-locals-correct

explicate-correct : ∀ {A} (P : Impμ.Program A) → ⟦ P ⟧ᵢ ＝ ⟦ explicate P ⟧ᶜ
explicate-correct = Explicate.explicate-correct

select-correct : ∀ {A} (P : CFGμ.Program A) → ⟦ P ⟧ᶜ ＝ ⟦ select P ⟧ₜ
select-correct = Select.select-correct

{- The whole compiler, for closed programs of any type ----------------------}

{- the compiled program produces the same constants as the original, and
   produces something exactly when the original does: into Clos5μ
   (compile), Monμ (compile-mon), Impμ (compile-imp), CFGμ (compile-cfg)
   and X86μ (compile-x86) -}

compile-correct-const : ∀ {A} (M : ISWIMμ.Tm [] A) (B : Base) (c : base-rep B)
  → (⟦ M ⟧ · ρ₀ ＝ const B c → ⟦ compile M ⟧₅ ＝ const B c)
  × (⟦ compile M ⟧₅ ＝ const B c → ⟦ M ⟧ · ρ₀ ＝ const B c)
compile-correct-const M = pr₁ (Compiler.compile-same M)

compile-correct-defined : ∀ {A} (M : ISWIMμ.Tm [] A)
  → (defined (⟦ M ⟧ · ρ₀) → defined ⟦ compile M ⟧₅)
  × (defined ⟦ compile M ⟧₅ → defined (⟦ M ⟧ · ρ₀))
compile-correct-defined M = pr₂ (Compiler.compile-same M)

compile-mon-correct-const : ∀ {A} (M : ISWIMμ.Tm [] A) (B : Base) (c : base-rep B)
  → (⟦ M ⟧ · ρ₀ ＝ const B c → ⟦ ⌜ compile-mon M ⌝ₚ ⟧₅ ＝ const B c)
  × (⟦ ⌜ compile-mon M ⌝ₚ ⟧₅ ＝ const B c → ⟦ M ⟧ · ρ₀ ＝ const B c)
compile-mon-correct-const M = pr₁ (Compiler.compile-mon-same M)

compile-mon-correct-defined : ∀ {A} (M : ISWIMμ.Tm [] A)
  → (defined (⟦ M ⟧ · ρ₀) → defined ⟦ ⌜ compile-mon M ⌝ₚ ⟧₅)
  × (defined ⟦ ⌜ compile-mon M ⌝ₚ ⟧₅ → defined (⟦ M ⟧ · ρ₀))
compile-mon-correct-defined M = pr₂ (Compiler.compile-mon-same M)

compile-imp-correct-const : ∀ {A} (M : ISWIMμ.Tm [] A) (B : Base) (c : base-rep B)
  → (⟦ M ⟧ · ρ₀ ＝ const B c → ⟦ compile-imp M ⟧ᵢ ＝ const B c)
  × (⟦ compile-imp M ⟧ᵢ ＝ const B c → ⟦ M ⟧ · ρ₀ ＝ const B c)
compile-imp-correct-const M = pr₁ (Compiler.compile-imp-same M)

compile-imp-correct-defined : ∀ {A} (M : ISWIMμ.Tm [] A)
  → (defined (⟦ M ⟧ · ρ₀) → defined ⟦ compile-imp M ⟧ᵢ)
  × (defined ⟦ compile-imp M ⟧ᵢ → defined (⟦ M ⟧ · ρ₀))
compile-imp-correct-defined M = pr₂ (Compiler.compile-imp-same M)

compile-cfg-correct-const : ∀ {A} (M : ISWIMμ.Tm [] A) (B : Base) (c : base-rep B)
  → (⟦ M ⟧ · ρ₀ ＝ const B c → ⟦ compile-cfg M ⟧ᶜ ＝ const B c)
  × (⟦ compile-cfg M ⟧ᶜ ＝ const B c → ⟦ M ⟧ · ρ₀ ＝ const B c)
compile-cfg-correct-const M = pr₁ (Compiler.compile-cfg-same M)

compile-cfg-correct-defined : ∀ {A} (M : ISWIMμ.Tm [] A)
  → (defined (⟦ M ⟧ · ρ₀) → defined ⟦ compile-cfg M ⟧ᶜ)
  × (defined ⟦ compile-cfg M ⟧ᶜ → defined (⟦ M ⟧ · ρ₀))
compile-cfg-correct-defined M = pr₂ (Compiler.compile-cfg-same M)

compile-x86-correct-const : ∀ {A} (M : ISWIMμ.Tm [] A) (B : Base) (c : base-rep B)
  → (⟦ M ⟧ · ρ₀ ＝ const B c → ⟦ compile-x86 M ⟧ₜ ＝ const B c)
  × (⟦ compile-x86 M ⟧ₜ ＝ const B c → ⟦ M ⟧ · ρ₀ ＝ const B c)
compile-x86-correct-const M = pr₁ (Compiler.compile-x86-same M)

compile-x86-correct-defined : ∀ {A} (M : ISWIMμ.Tm [] A)
  → (defined (⟦ M ⟧ · ρ₀) → defined ⟦ compile-x86 M ⟧ₜ)
  × (defined ⟦ compile-x86 M ⟧ₜ → defined (⟦ M ⟧ · ρ₀))
compile-x86-correct-defined M = pr₂ (Compiler.compile-x86-same M)

{- The end-to-end theorem, for a main program of type Int -}

compile-x86-int-const : ∀ (M : ISWIMμ.Tm [] (base Int)) (B : Base) (c : base-rep B)
  → (⟦ M ⟧ · ρ₀ ＝ const B c → ⟦ compile-x86 M ⟧ₜ ＝ const B c)
  × (⟦ compile-x86 M ⟧ₜ ＝ const B c → ⟦ M ⟧ · ρ₀ ＝ const B c)
compile-x86-int-const M = pr₁ (Compiler.compile-x86-int M)

compile-x86-int-defined : ∀ (M : ISWIMμ.Tm [] (base Int))
  → (defined (⟦ M ⟧ · ρ₀) → defined ⟦ compile-x86 M ⟧ₜ)
  × (defined ⟦ compile-x86 M ⟧ₜ → defined (⟦ M ⟧ · ρ₀))
compile-x86-int-defined M = pr₂ (Compiler.compile-x86-int M)
