{-

  Correctness of the compiler into CFG and into X86, by CEK machines and
  forward simulations: the compiler into Imp (LiftLocalsSim), then
  explicate control (ExplicateSim) and select instructions (SelectSim).
  Those two proofs are between machines of first-order languages, and
  are shared with the reduction-semantics proof.

-}

module Untyped.proof.Correctness.CEK.CompilerX86Sim where

open import Untyped.Compiler.Pipeline using (compile-imp; compile-cfg; compile-x86)
open import Untyped.proof.Compiler.CaptureScope using (Closed)
open import proof.Semantics.CEK.Simulation using (Equivalent; equiv-trans)
open import Untyped.proof.Correctness.CEK.LiftLocalsSim using (compile-imp-correct)
open import Untyped.proof.Correctness.CEK.ExplicateSim using (explicate-correct)
open import Untyped.proof.Correctness.CEK.SelectSim using (select-correct)
import Semantics.CEK.ISWIM as S
import Untyped.Semantics.CEK.CFG as G
import Semantics.CEK.X86 as X

compile-cfg-correct : ∀ M → Closed M → Equivalent (S.sem M) (G.sem (compile-cfg M))
compile-cfg-correct M c = equiv-trans (compile-imp-correct M c) (explicate-correct (compile-imp M))

compile-x86-correct : ∀ M → Closed M → Equivalent (S.sem M) (X.sem (compile-x86 M))
compile-x86-correct M c = equiv-trans (compile-cfg-correct M c) (select-correct (compile-cfg M))
