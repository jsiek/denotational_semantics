{-

  SPECIFICATION (phase 2 of the typed port; not proved here): the
  statements of Theorems/Simulation.agda for the typed compiler
  (Compiler/Typed/Pipeline.agda), CEK machines + forward simulations.
  Same shapes as today: Equivalent per pass and end to end.

  Machines (to write, phase 2, CEK column; the first four exist from the
  pilot):
    ISWIMₘ  = Semantics.CEK.ISWIM               (untyped, unchanged)
    ISWIMᵀₘ = Semantics.CEK.Typed.ISWIM         Clos2ᵀₘ = Semantics.CEK.Typed.Clos2
    Clos3ᵀₘ = Semantics.CEK.Typed.Clos3         Clos4ᵀₘ = Semantics.CEK.Typed.Clos4
    Clos5ᵀₘ = Semantics.CEK.Typed.Clos5         (sem : Clos5ᵀ.Program → Machine)
    Impᵀₘ   = Semantics.CEK.Typed.Imp           (sem : Impᵀ.Program → Machine)
    CFGᵀₘ   = Semantics.CEK.Typed.CFG           (sem : CFGᵀ.Program → Machine)
    X86ₘ    = Semantics.CEK.X86                 (untyped, unchanged)
  Monᵀ has no machine: a Monᵀ program runs as its embedding ⌜ P ⌝ₚ
  (Language/Typed/Mon.agda) on the Clos5ᵀ machine.

  -- each pass
  simplify-correct   : ∀ (M : ISWIM.AST) → Closed M
    → Equivalent (ISWIMₘ.sem M) (ISWIMₘ.sem (simplify M))            -- unchanged
  cast-correct       : ∀ (M : ISWIM.AST) → Closed M
    → Equivalent (ISWIMₘ.sem M) (ISWIMᵀₘ.sem (cast-closed M))
  enclose-correct    : ∀ (M : ISWIMᵀ.Tm 0 Any) → Equivalent (ISWIMᵀₘ.sem M) (Clos2ᵀₘ.sem (enclose M))
  optimize-correct   : ∀ (M : Clos2ᵀ.Tm 0 Any) → Equivalent (Clos2ᵀₘ.sem M) (Clos2ᵀₘ.sem (optimize-program M))
  concretize-correct : ∀ (M : Clos2ᵀ.Tm 0 Any) → Equivalent (Clos2ᵀₘ.sem M) (Clos3ᵀₘ.sem (concretize-program M))
  delay-correct      : ∀ (M : Clos3ᵀ.Tm [] Any) → Equivalent (Clos3ᵀₘ.sem M) (Clos4ᵀₘ.sem (delay-program M))
  globalize-correct  : ∀ (M : Clos4ᵀ.Tm [] Any) → Equivalent (Clos4ᵀₘ.sem M) (Clos5ᵀₘ.sem (globalize M))
  rco-correct        : ∀ (P : Clos5ᵀ.Program) → Equivalent (Clos5ᵀₘ.sem P) (Clos5ᵀₘ.sem ⌜ rco-program P ⌝ₚ)
  lift-locals-correct : ∀ (P : Monᵀ.Program) → Equivalent (Clos5ᵀₘ.sem ⌜ P ⌝ₚ) (Impᵀₘ.sem (lift-program P))
  explicate-correct  : ∀ (P : Impᵀ.Program) → Equivalent (Impᵀₘ.sem P) (CFGᵀₘ.sem (explicate P))
  select-correct     : ∀ (P : CFGᵀ.Program) → Equivalent (CFGᵀₘ.sem P) (X86ₘ.sem (select P))
     -- X86 keeps its own trapped errors (an unset register, a missing
     -- label or flag, a slot beyond the frame, a value of the wrong kind
     -- other than at a project's test): the proof shows that select's
     -- code never reaches them. If that needs a well-formedness
     -- precondition, state it and discharge it for compile-cfg's output.

  -- the whole compiler, for closed programs (Compiler/Typed/Pipeline.agda)
  compile-correct     : ∀ (M : ISWIM.AST) → Closed M → Equivalent (ISWIMₘ.sem M) (Clos5ᵀₘ.sem (compile M))
  compile-mon-correct : ∀ (M : ISWIM.AST) → Closed M → Equivalent (ISWIMₘ.sem M) (Clos5ᵀₘ.sem ⌜ compile-mon M ⌝ₚ)
  compile-imp-correct : ∀ (M : ISWIM.AST) → Closed M → Equivalent (ISWIMₘ.sem M) (Impᵀₘ.sem (compile-imp M))
  compile-cfg-correct : ∀ (M : ISWIM.AST) → Closed M → Equivalent (ISWIMₘ.sem M) (CFGᵀₘ.sem (compile-cfg M))
  compile-x86-correct : ∀ (M : ISWIM.AST) → Closed M → Equivalent (ISWIMₘ.sem M) (X86ₘ.sem (compile-x86 M))
  compile-const, compile-converges, compile-error, compile-diverges   -- as today, for compile

  The precondition Closed M becomes WS 0 (simplify M), and
  cast-closed (simplify M) the cast-program of it, by
  proof/Compiler/Typed/CastScope.agda (simplify-ws, cast-closed-≡).
  No other precondition (Scoped, MonProgram, WS 0) is needed: the typed
  syntax has no free variables and Monᵀ is monadic by construction.

-}

module proof.Spec.Typed.Simulation where
