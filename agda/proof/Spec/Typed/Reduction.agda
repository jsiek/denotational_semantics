{-

  SPECIFICATION (phase 2 of the typed port; not proved here): the
  statements of Theorems/Reduction.agda for the typed compiler
  (Compiler/Typed/Pipeline.agda), reduction semantics + simulations.
  Same shapes as today: Equivalent per pass and end to end.

  Reduction semantics (to write, phase 2, reduction column), by
  substitution, for the languages with binders:
    ISWIMᵣ  = Semantics.Reduction.ISWIM             (untyped, unchanged)
    ISWIMᵀᵣ = Semantics.Reduction.Typed.ISWIM  Clos2ᵀᵣ = Semantics.Reduction.Typed.Clos2
    Clos3ᵀᵣ = Semantics.Reduction.Typed.Clos3  Clos4ᵀᵣ = Semantics.Reduction.Typed.Clos4
    Clos5ᵀᵣ = Semantics.Reduction.Typed.Clos5  (sem : Clos5ᵀ.Program → Machine)
  Typed substitution of typed terms (a typed variant of
  Framework/Syntax/Subst.agda, language independent, may be
  infrastructure). As today, Impᵀ, CFGᵀ and X86 have no binders: the
  reduction column uses the CEK column's machines of Impᵀ, CFGᵀ and X86
  and shares the explicate and select proofs with it (owned by CEK).

  -- each pass
  simplify-correct   : ∀ (M : ISWIM.AST) → Closed M
    → Equivalent (ISWIMᵣ.sem M) (ISWIMᵣ.sem (simplify M))            -- unchanged
  cast-correct       : ∀ (M : ISWIM.AST) → Closed M → Equivalent (ISWIMᵣ.sem M) (ISWIMᵀᵣ.sem (cast-closed M))
  enclose-correct    : ∀ (M : ISWIMᵀ.Tm 0 Any) → Equivalent (ISWIMᵀᵣ.sem M) (Clos2ᵀᵣ.sem (enclose M))
  optimize-correct   : ∀ (M : Clos2ᵀ.Tm 0 Any) → Equivalent (Clos2ᵀᵣ.sem M) (Clos2ᵀᵣ.sem (optimize-program M))
  concretize-correct : ∀ (M : Clos2ᵀ.Tm 0 Any) → Equivalent (Clos2ᵀᵣ.sem M) (Clos3ᵀᵣ.sem (concretize-program M))
     -- no WS 0 precondition: typed terms are closed by construction
  delay-correct      : ∀ (M : Clos3ᵀ.Tm [] Any) → Equivalent (Clos3ᵀᵣ.sem M) (Clos4ᵀᵣ.sem (delay-program M))
  globalize-correct  : ∀ (M : Clos4ᵀ.Tm [] Any) → Equivalent (Clos4ᵀᵣ.sem M) (Clos5ᵀᵣ.sem (globalize M))
  rco-correct        : ∀ (P : Clos5ᵀ.Program) → Equivalent (Clos5ᵀᵣ.sem P) (Clos5ᵀᵣ.sem ⌜ rco-program P ⌝ₚ)
  lift-locals-correct : ∀ (P : Monᵀ.Program) → Equivalent (Clos5ᵀᵣ.sem ⌜ P ⌝ₚ) (Impᵀₘ.sem (lift-program P))
  explicate-correct  : ∀ (P : Impᵀ.Program) → Equivalent (Impᵀₘ.sem P) (CFGᵀₘ.sem (explicate P))   -- the CEK proof
  select-correct     : ∀ (P : CFGᵀ.Program) → Equivalent (CFGᵀₘ.sem P) (X86ₘ.sem (select P))     -- the CEK proof

  -- the whole compiler, for closed programs
  compile-correct     : ∀ (M : ISWIM.AST) → Closed M → Equivalent (ISWIMᵣ.sem M) (Clos5ᵀᵣ.sem (compile M))
  compile-mon-correct : ∀ (M : ISWIM.AST) → Closed M → Equivalent (ISWIMᵣ.sem M) (Clos5ᵀᵣ.sem ⌜ compile-mon M ⌝ₚ)
  compile-imp-correct : ∀ (M : ISWIM.AST) → Closed M → Equivalent (ISWIMᵣ.sem M) (Impᵀₘ.sem (compile-imp M))
  compile-cfg-correct : ∀ (M : ISWIM.AST) → Closed M → Equivalent (ISWIMᵣ.sem M) (CFGᵀₘ.sem (compile-cfg M))
  compile-x86-correct : ∀ (M : ISWIM.AST) → Closed M → Equivalent (ISWIMᵣ.sem M) (X86ₘ.sem (compile-x86 M))
  compile-const, compile-converges, compile-error, compile-diverges   -- as today, for compile

-}

module proof.Spec.Typed.Reduction where
