{-

  Correctness of the compiler into CFG and into X86, by reduction
  semantics and forward simulations: the compiler into Imp
  (LiftLocalsRed), then explicate control and select instructions, whose
  proofs between the machines of the first-order languages Imp, CFG and
  X86 are shared with the CEK machine + simulation proof (ExplicateSim,
  SelectSim).

-}

module Untyped.proof.Correctness.Reduction.CompilerX86Red where

open import Untyped.Compiler.Pipeline using (compile-imp; compile-cfg; compile-x86)
open import Untyped.proof.Compiler.EncloseScope using (Closed)
open import proof.Semantics.CEK.Simulation using (Equivalent; equiv-trans)
open import Untyped.proof.Correctness.Reduction.LiftLocalsRed using (compile-imp-correct)
open import Untyped.proof.Correctness.CEK.ExplicateSim using (explicate-correct)
open import Untyped.proof.Correctness.CEK.SelectSim using (select-correct)
import Semantics.Reduction.ISWIM as S
import Untyped.Semantics.CEK.CFG as G
import Semantics.CEK.X86 as X

compile-cfg-correct : ∀ M → Closed M → Equivalent (S.sem M) (G.sem (compile-cfg M))
compile-cfg-correct M c = equiv-trans (compile-imp-correct M c) (explicate-correct (compile-imp M))

compile-x86-correct : ∀ M → Closed M → Equivalent (S.sem M) (X.sem (compile-x86 M))
compile-x86-correct M c = equiv-trans (compile-cfg-correct M c) (select-correct (compile-cfg M))
