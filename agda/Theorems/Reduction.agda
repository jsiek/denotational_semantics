{-

  The correctness of the compiler, by reduction semantics and
  simulations: the public statements.
  The proofs (forward simulations) are in
  proof/Compiler/Reduction/Correctness/; each theorem here is one of
  them, with its type written out, so that it can be read without opening
  proof/.

    ISWIM --enclose--> Clos2 --optimize--> Clos2 --concretize--> Clos3
          --delay--> Clos4 --globalize--> Clos5 --rco--> Clos5
          --lift locals--> Imp --explicate control--> CFG
          --select instructions--> X86

  Each language with binders has a reduction semantics by substitution
  (Compiler/Reduction/, here Lᵣ.sem for language L), which terminates
  with an observation (Compiler/Observation.agda) or diverges; Imp, CFG
  and X86 have no binders and keep their machines
  (Compiler/Operational/Machine/, here Lₘ.sem). Two semantics are
  Equivalent (Framework/Smallstep.agda) when each terminates with o
  exactly when the other does (o-wrong, going wrong, included), and one
  diverges exactly when the other does.

  To read them: the languages (Compiler/Lang/), the passes
  (Compiler/Compile/), the semantics, the observations, and the
  preconditions: Closed (Compiler/Compile/EncloseScope.agda), WS
  (Framework/Syntax/Scope.agda) and Scoped
  (Compiler/Compile/PipelineScope.agda).

-}

module Theorems.Reduction where

open import Compiler.Observation using (o-const; o-wrong; Converges; _⇔_)
open import Compiler.Reduction.Smallstep using (Terminates; Diverges; Equivalent)

import Compiler.Lang.ISWIM as ISWIM
import Compiler.Lang.Clos2 as Clos2
import Compiler.Lang.Clos3 as Clos3
import Compiler.Lang.Clos4 as Clos4
import Compiler.Lang.Clos5 as Clos5

open import Compiler.Compile.Enclose using (enclose)
open import Compiler.Compile.Optimize using (optimize-program)
open import Compiler.Compile.Concretize using (concretize-program)
open import Compiler.Compile.Delay using (delay)
open import Compiler.Compile.Globalize using (globalize)
open import Compiler.Compile.RCO using (rco-program)
open import Compiler.Compile.Pipeline using (compile; compile-mon)

open import Compiler.Compile.EncloseScope using (Closed)
open import Framework.Syntax.Scope Clos2.Op Clos2.sig using (WS)
open import Compiler.Compile.PipelineScope using (Scoped)

import Compiler.Reduction.ISWIM as ISWIMᵣ
import Compiler.Reduction.Clos2 as Clos2ᵣ
import Compiler.Reduction.Clos3 as Clos3ᵣ
import Compiler.Reduction.Clos4 as Clos4ᵣ
import Compiler.Reduction.Clos5 as Clos5ᵣ

import proof.Compiler.Reduction.Correctness.EncloseRed as EncloseRed
import proof.Compiler.Reduction.Correctness.OptimizeRed as OptimizeRed
import proof.Compiler.Reduction.Correctness.ConcretizeRed as ConcretizeRed
import proof.Compiler.Reduction.Correctness.DelayRed as DelayRed
import proof.Compiler.Reduction.Correctness.GlobalizeRed as GlobalizeRed
import proof.Compiler.Reduction.Correctness.CompilerRed as CompilerRed
import proof.Compiler.Reduction.Correctness.RCORed as RCORed

{- Each pass ------------------------------------------------------------------}

{- enclose, for closed programs -}
enclose-correct : ∀ (M : ISWIM.AST) → Closed M
  → Equivalent (ISWIMᵣ.sem M) (Clos2ᵣ.sem (enclose M))
enclose-correct = EncloseRed.enclose-correct

{- optimize, for well-scoped programs (which enclose produces) -}
optimize-correct : ∀ (M : Clos2.AST) → WS 0 M
  → Equivalent (Clos2ᵣ.sem M) (Clos2ᵣ.sem (optimize-program M))
optimize-correct = OptimizeRed.optimize-correct

{- concretize, for well-scoped programs (which optimize produces) -}
concretize-correct : ∀ (M : Clos2.AST) → WS 0 M
  → Equivalent (Clos2ᵣ.sem M) (Clos3ᵣ.sem (concretize-program M))
concretize-correct = ConcretizeRed.concretize-correct

delay-correct : ∀ (M : Clos3.AST) → Equivalent (Clos3ᵣ.sem M) (Clos4ᵣ.sem (delay M))
delay-correct = DelayRed.delay-correct

globalize-correct : ∀ (M : Clos4.AST) → Equivalent (Clos4ᵣ.sem M) (Clos5ᵣ.sem (globalize M))
globalize-correct = GlobalizeRed.globalize-correct

{- remove complex operands, for well-scoped programs (which the compiler
   produces) -}
rco-correct : ∀ (P : Clos5.Program) → Scoped P
  → Equivalent (Clos5ᵣ.sem P) (Clos5ᵣ.sem (rco-program P))
rco-correct = RCORed.rco-correct

{- The whole compiler, for closed programs ----------------------------------}

compile-correct : ∀ (M : ISWIM.AST) → Closed M
  → Equivalent (ISWIMᵣ.sem M) (Clos5ᵣ.sem (compile M))
compile-correct = CompilerRed.compile-correct

compile-mon-correct : ∀ (M : ISWIM.AST) → Closed M
  → Equivalent (ISWIMᵣ.sem M) (Clos5ᵣ.sem (compile-mon M))
compile-mon-correct = RCORed.compile-mon-correct

{- in particular, for compile: the compiled program terminates with the
   same constants, terminates with an answer exactly when the original
   does, goes wrong exactly when it does, and diverges exactly when it
   does -}

compile-const : ∀ (M : ISWIM.AST) → Closed M → ∀ B k
  → Terminates (ISWIMᵣ.sem M) (o-const B k) ⇔ Terminates (Clos5ᵣ.sem (compile M)) (o-const B k)
compile-const = CompilerRed.compile-const

compile-converges : ∀ (M : ISWIM.AST) → Closed M
  → Converges (Terminates (ISWIMᵣ.sem M)) ⇔ Converges (Terminates (Clos5ᵣ.sem (compile M)))
compile-converges = CompilerRed.compile-converges

compile-wrong : ∀ (M : ISWIM.AST) → Closed M
  → Terminates (ISWIMᵣ.sem M) o-wrong ⇔ Terminates (Clos5ᵣ.sem (compile M)) o-wrong
compile-wrong = CompilerRed.compile-wrong

compile-diverges : ∀ (M : ISWIM.AST) → Closed M
  → Diverges (ISWIMᵣ.sem M) ⇔ Diverges (Clos5ᵣ.sem (compile M))
compile-diverges = CompilerRed.compile-diverges
