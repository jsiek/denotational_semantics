{-

  Correctness of the compiler into CFG and into X86, by reduction
  semantics and forward simulations: the compiler into Imp
  (LiftLocalsRed), then explicate control and select instructions, whose
  proofs between the machines of the first-order languages Imp, CFG and
  X86 are shared with the CEK machine + simulation proof (ExplicateSim,
  SelectSim).

-}

module proof.Compiler.Reduction.Correctness.CompilerX86Red where

open import Compiler.Compile.Pipeline using (compile-imp; compile-cfg; compile-x86)
open import proof.Compiler.Compile.EncloseScope using (Closed)
open import proof.Compiler.Operational.Simulation using (Equivalent; equiv-trans)
open import proof.Compiler.Reduction.Correctness.LiftLocalsRed using (compile-imp-correct)
open import proof.Compiler.Operational.Correctness.ExplicateSim using (explicate-correct)
open import proof.Compiler.Operational.Correctness.SelectSim using (select-correct)
import Compiler.Reduction.ISWIM as S
import Compiler.Operational.Machine.CFG as G
import Compiler.Operational.Machine.X86 as X

compile-cfg-correct : ∀ M → Closed M → Equivalent (S.sem M) (G.sem (compile-cfg M))
compile-cfg-correct M c = equiv-trans (compile-imp-correct M c) (explicate-correct (compile-imp M))

compile-x86-correct : ∀ M → Closed M → Equivalent (S.sem M) (X.sem (compile-x86 M))
compile-x86-correct M c = equiv-trans (compile-cfg-correct M c) (select-correct (compile-cfg M))
