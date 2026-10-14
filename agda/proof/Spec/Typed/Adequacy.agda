{-

  SPECIFICATION (phase 2 of the typed port; not proved here): the
  statements of Theorems/Adequacy.agda for the typed compiler
  (Compiler/Typed/Pipeline.agda): the plain graph model (Spec/Typed/
  Denotational.agda) against the machines. Same shapes as today.

  Machines: the ISWIM machine (Semantics.CEK.ISWIM, unchanged), the
  Clos5ᵀ machine (Semantics.CEK.Typed.Clos5, the CEK column's) and the X86
  machine (Semantics.CEK.X86, unchanged). Semantics: ⟦_⟧ (untyped ISWIM,
  unchanged), ⟦_⟧₅ and ⟦_⟧ₓ (Spec/Typed/Denotational.agda).

  -- the ISWIM machine: unchanged
  iswim-const-iff, iswim-nonempty-iff, iswim-error-empty, iswim-diverges-empty
  compile-correct-machine-const : ∀ (M : ISWIM.AST) → Closed M → ∀ {B} (k : base-rep B)
    → Terminates (ISWIMₘ.sem M) (o-const B k) ⇔ (const k ∈ ⟦ compile M ⟧₅)
  compile-correct-machine-converges : ∀ (M : ISWIM.AST) → Closed M
    → Converges (Terminates (ISWIMₘ.sem M)) ⇔ nonempty ⟦ compile M ⟧₅

  -- the Clos5ᵀ machine, for the programs compile produces
  clos5-const-iff : ∀ (M : ISWIM.AST) → Closed M → ∀ {B} {k : base-rep B}
    → (const k ∈ ⟦ compile M ⟧₅) ⇔ Terminates (Clos5ᵀₘ.sem (compile M)) (o-const B k)
  clos5-nonempty-iff, clos5-error-empty, clos5-diverges-empty      -- likewise

  -- the X86 machine, for the programs compile-x86 produces
  x86-const-iff, x86-nonempty-iff                                  -- on compile-x86 M, as today

  -- end to end, through the machines only
  end-to-end-const, end-to-end-converges, end-to-end-x86-const, end-to-end-x86-converges

  The well-formedness facts adequacy needs of compiled programs
  (today Clos5WF, X86WF: references only to older definitions, slots
  within the frame, a consistent table) shrink: typed syntax rules out
  missing definitions, slots and labels; what remains is the order of
  the table (references only to older definitions) and select's frames.

-}

module proof.Spec.Typed.Adequacy where
