{-

  SPECIFICATION (phase 2 of the typed port; not proved here): the
  statements of Theorems/Denotational.agda for the typed compiler
  (Compiler/Typed/Pipeline.agda), in the (plain) graph model. Same
  shapes as today: ≃ per pass but delay; delay and the compositions on
  constants and nonemptiness.

  Semantics (to write, phase 2, graph-model column), by recursion on
  typed terms, with the graph model's operators (no error monad; the
  typed graph model with errors, Semantics/GraphErr/Typed/, is the
  template, and the infrastructure proof/Framework/GraphModel/{TypedOk,
  TypedBinders}.agda gives monotonicity, consistency and continuity):
    ⟦_⟧  = Semantics.Graph.ISWIM                    (untyped, unchanged)
    ⟦_⟧ᵀ = Semantics.Graph.Typed.ISWIM   ⟦_⟧₂ = Semantics.Graph.Typed.Clos2
    ⟦_⟧₃ = Semantics.Graph.Typed.Clos3   ⟦_⟧₄ = Semantics.Graph.Typed.Clos4
    ⟦_⟧₅ = Semantics.Graph.Typed.Clos5   (⟦_⟧₅ : Clos5ᵀ.Program → 𝒫 Value)
    ⟦_⟧ᵢ = Semantics.Graph.Typed.Imp (continuation-passing, as ImpK today)
    ⟦_⟧ᶜ = Semantics.Graph.Typed.CFG     ⟦_⟧ₓ = Semantics.Graph.X86 (untyped, unchanged)
  In the plain graph model a failed project denotes ∅, as an error does
  today. The table of definitions is typed over the whole table (a
  definition may refer to any, itself included); a graph semantics needs
  a well-founded table, so, as today (Semantics/Graph/Clos5Iswim.agda),
  a definition sees only the older ones, and a reference to another is
  code that never returns. Globalize makes only references to older
  definitions; the proofs of globalize and adequacy need that fact
  (shared with the graph model with errors).

  -- each pass
  simplify-correct   : ∀ (M : ISWIM.AST) → ⟦ M ⟧ ρ₀ ≃ ⟦ simplify M ⟧ ρ₀            -- unchanged
  cast-correct       : ∀ (M : ISWIM.AST) → Closed M → ⟦ M ⟧ ρ₀ ≃ ⟦ cast-closed M ⟧ᵀ ρ₀
  enclose-correct    : ∀ (M : ISWIMᵀ.Tm 0 Any) → ⟦ M ⟧ᵀ ρ₀ ≃ ⟦ enclose M ⟧₂ ρ₀
  optimize-correct   : ∀ (M : Clos2ᵀ.Tm 0 Any) → ⟦ M ⟧₂ ρ₀ ≃ ⟦ optimize-program M ⟧₂ ρ₀
  concretize-correct : ∀ (M : Clos2ᵀ.Tm 0 Any) → ⟦ M ⟧₂ ρ₀ ≃ ⟦ concretize-program M ⟧₃ ρ₀
  delay-correct-const    : ∀ (M : Clos3ᵀ.Tm [] Any) {B} (c : base-rep B)
    → (const c ∈ ⟦ M ⟧₃ ρ₀ → const c ∈ ⟦ delay-program M ⟧₄ ρ₀) × (the converse)
  delay-correct-nonempty : ∀ (M : Clos3ᵀ.Tm [] Any)
    → (nonempty (⟦ M ⟧₃ ρ₀) → nonempty (⟦ delay-program M ⟧₄ ρ₀)) × (the converse)
  globalize-correct  : ∀ (M : Clos4ᵀ.Tm [] Any) → ⟦ M ⟧₄ ρ₀ ≃ ⟦ globalize M ⟧₅
  rco-correct        : ∀ (P : Clos5ᵀ.Program) → ⟦ ⌜ rco-program P ⌝ₚ ⟧₅ ≃ ⟦ P ⟧₅
  lift-locals-correct : ∀ (P : Monᵀ.Program) → ⟦ lift-program P ⟧ᵢ ≃ ⟦ ⌜ P ⌝ₚ ⟧₅
  explicate-correct  : ∀ (P : Impᵀ.Program) → ⟦ explicate P ⟧ᶜ ≃ ⟦ P ⟧ᵢ
  select-correct     : ∀ (P : CFGᵀ.Program) → ⟦ select P ⟧ₓ ≃ ⟦ P ⟧ᶜ
     -- today's precondition (2 ≤ locals of each definition) holds by
     -- construction (select's frame is at least its entry context, 2);
     -- any other precondition of X86's semantics is discharged for
     -- compile-cfg's output

  -- the whole compiler, for closed programs: the same constants, and
  -- nonempty together, for compile, compile-mon (via ⌜_⌝ₚ), compile-imp,
  -- compile-cfg and compile-x86
  compile-correct-const    : ∀ (M : ISWIM.AST) → Closed M → ∀ {B} (c : base-rep B)
    → (const c ∈ ⟦ M ⟧ ρ₀ → const c ∈ ⟦ compile M ⟧₅) × (the converse)
  compile-correct-nonempty : ∀ (M : ISWIM.AST) → Closed M
    → (nonempty (⟦ M ⟧ ρ₀) → nonempty ⟦ compile M ⟧₅) × (the converse)
  … and likewise -mon, -imp, -cfg, -x86.
  (Today's statements have no Closed M; the typed ones need it, for
  cast insertion.)

-}

module proof.Spec.Typed.Denotational where
