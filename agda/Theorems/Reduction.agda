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
  (Compiler/Operational/Machine/). Two semantics are Equivalent
  (Framework/Smallstep.agda) when each terminates with o exactly when the
  other does (o-wrong, going wrong, included), and one diverges exactly
  when the other does.

  To read them: the languages (Compiler/Lang/), the passes
  (Compiler/Compile/), the semantics, the observations, and the
  preconditions: Closed (Compiler/Compile/EncloseScope.agda).

-}

module Theorems.Reduction where

open import Compiler.Reduction.Smallstep using (Equivalent)

import Compiler.Lang.ISWIM as ISWIM

open import Compiler.Compile.Enclose using (enclose)

open import Compiler.Compile.EncloseScope using (Closed)

import Compiler.Reduction.ISWIM as ISWIMᵣ
import Compiler.Reduction.Clos2 as Clos2ᵣ

import proof.Compiler.Reduction.Correctness.EncloseRed as EncloseRed

{- Each pass ------------------------------------------------------------------}

{- enclose, for closed programs -}
enclose-correct : ∀ (M : ISWIM.AST) → Closed M
  → Equivalent (ISWIMᵣ.sem M) (Clos2ᵣ.sem (enclose M))
enclose-correct = EncloseRed.enclose-correct
