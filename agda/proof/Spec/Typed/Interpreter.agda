{-

  SPECIFICATION (phase 2 of the typed port; not proved here): the
  statements of Theorems/Interpreter.agda for the typed compiler
  (Compiler/Typed/Pipeline.agda), clocked interpreters + value relations.
  Same shapes as today: Equivalent (at the interpreters' observations,
  Semantics/Interp/Clock.agda) per pass and end to end.

  Interpreters (to write, phase 2, interpreter column):
    ISWIMᵢ  = Semantics.Interp.ISWIM                (untyped, unchanged)
    ISWIMᵀᵢ = Semantics.Interp.Typed.ISWIM   Clos2ᵀᵢ = Semantics.Interp.Typed.Clos2
    Clos3ᵀᵢ = Semantics.Interp.Typed.Clos3   Clos4ᵀᵢ = Semantics.Interp.Typed.Clos4
    Clos5ᵀᵢ = Semantics.Interp.Typed.Clos5   (sem : Clos5ᵀ.Program → …)
    Impᵀᵢ   = Semantics.Interp.Typed.Imp     CFGᵀᵢ = Semantics.Interp.Typed.CFG
    X86ᵢ    = Semantics.Interp.X86                  (untyped, unchanged)
  A typed interpreter is a total function of typed terms to typed values
  (with the clock); it errs only at a failed project (and times out).
  Monᵀ runs as its embedding ⌜ P ⌝ₚ on the Clos5ᵀ interpreter.

  -- each pass
  simplify-correct   : ∀ (M : ISWIM.AST) → Closed M
    → Equivalent (ISWIMᵢ.sem M) (ISWIMᵢ.sem (simplify M))            -- unchanged
  cast-correct       : ∀ (M : ISWIM.AST) → Closed M → Equivalent (ISWIMᵢ.sem M) (ISWIMᵀᵢ.sem (cast-closed M))
  enclose-correct    : ∀ (M : ISWIMᵀ.Tm 0 Any) → Equivalent (ISWIMᵀᵢ.sem M) (Clos2ᵀᵢ.sem (enclose M))
  optimize-correct   : ∀ (M : Clos2ᵀ.Tm 0 Any) → Equivalent (Clos2ᵀᵢ.sem M) (Clos2ᵀᵢ.sem (optimize-program M))
  concretize-correct : ∀ (M : Clos2ᵀ.Tm 0 Any) → Equivalent (Clos2ᵀᵢ.sem M) (Clos3ᵀᵢ.sem (concretize-program M))
  delay-correct      : ∀ (M : Clos3ᵀ.Tm [] Any) → Equivalent (Clos3ᵀᵢ.sem M) (Clos4ᵀᵢ.sem (delay-program M))
  globalize-correct  : ∀ (M : Clos4ᵀ.Tm [] Any) → Equivalent (Clos4ᵀᵢ.sem M) (Clos5ᵀᵢ.sem (globalize M))
  rco-correct        : ∀ (P : Clos5ᵀ.Program) → Equivalent (Clos5ᵀᵢ.sem P) (Clos5ᵀᵢ.sem ⌜ rco-program P ⌝ₚ)
  lift-locals-correct : ∀ (P : Monᵀ.Program) → Equivalent (Clos5ᵀᵢ.sem ⌜ P ⌝ₚ) (Impᵀᵢ.sem (lift-program P))
  explicate-correct  : ∀ (P : Impᵀ.Program) → Equivalent (Impᵀᵢ.sem P) (CFGᵀᵢ.sem (explicate P))
  select-correct     : ∀ (P : CFGᵀ.Program) → Equivalent (CFGᵀᵢ.sem P) (X86ᵢ.sem (select P))
     -- as in Spec/Typed/Simulation.agda: X86's own errors are unreachable

  -- the whole compiler, for closed programs
  compile-correct, compile-mon-correct, compile-imp-correct,
  compile-cfg-correct, compile-x86-correct     -- as in Spec/Typed/Simulation.agda
  compile-const, compile-converges, compile-error, compile-diverges

  Clock for clock where today's proofs are; simplify keeps its
  clock-monotone proof.

-}

module proof.Spec.Typed.Interpreter where
