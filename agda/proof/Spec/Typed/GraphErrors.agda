{-

  SPECIFICATION (phase 2 of the typed port; not proved here): the
  statements of Theorems/GraphErrors.agda for the typed compiler
  (Compiler/Typed/Pipeline.agda), in the graph model with errors. Same
  shapes as today: ≃ per pass but delay; delay on errors, constants and
  values; Same end to end; adequacy for the ISWIM, Clos5ᵀ and X86
  machines on all three outcomes.

  Semantics (the first four exist from the pilot, Semantics/GraphErr/Typed/):
    ⟦_⟧  = Semantics.GraphErr.ISWIM                  (untyped, unchanged)
    ⟦_⟧ᵀ = Semantics.GraphErr.Typed.ISWIM  ⟦_⟧₂ = Semantics.GraphErr.Typed.Clos2
    ⟦_⟧₃ = Semantics.GraphErr.Typed.Clos3  ⟦_⟧₄ = Semantics.GraphErr.Typed.Clos4
    ⟦_⟧₅ = Semantics.GraphErr.Typed.Clos5  (⟦_⟧₅ : Clos5ᵀ.Program → 𝒫 Value)
    ⟦_⟧ᵢ = Semantics.GraphErr.Typed.Imp    ⟦_⟧ᶜ = Semantics.GraphErr.Typed.CFG
    ⟦_⟧ₓ = Semantics.GraphErr.X86                    (untyped, unchanged)
  ω arises only from project (and, in X86, from its own errors, which
  compiled code never reaches). The table of definitions: as in
  Spec/Typed/Denotational.agda (a definition sees the older ones; a
  reference to another is errcode, as today; globalize makes only
  references to older ones).

  -- each pass
  simplify-correct   : ∀ (M : ISWIM.AST) → Closed M → ⟦ M ⟧ ρ₀ ≃ ⟦ simplify M ⟧ ρ₀   -- unchanged
  cast-correct       : ∀ (M : ISWIM.AST) → Closed M → ⟦ M ⟧ ρ₀ ≃ ⟦ cast-closed M ⟧ᵀ ρ₀
  enclose-correct    : ∀ (M : ISWIMᵀ.Tm 0 Any) → ⟦ M ⟧ᵀ ρ₀ ≃ ⟦ enclose M ⟧₂ ρ₀
  optimize-correct   : ∀ (M : Clos2ᵀ.Tm 0 Any) → ⟦ M ⟧₂ ρ₀ ≃ ⟦ optimize-program M ⟧₂ ρ₀
  concretize-correct : ∀ (M : Clos2ᵀ.Tm 0 Any) → ⟦ M ⟧₂ ρ₀ ≃ ⟦ concretize-program M ⟧₃ ρ₀
  delay-correct-error / -const / -val : ∀ (M : Clos3ᵀ.Tm [] Any) → …  (as today, with delay-program)
  globalize-correct  : ∀ (M : Clos4ᵀ.Tm [] Any) → ⟦ M ⟧₄ ρ₀ ≃ ⟦ globalize M ⟧₅
  rco-correct        : ∀ (P : Clos5ᵀ.Program) → ⟦ ⌜ rco-program P ⌝ₚ ⟧₅ ≃ ⟦ P ⟧₅
  lift-locals-correct : ∀ (P : Monᵀ.Program) → ⟦ lift-program P ⟧ᵢ ≃ ⟦ ⌜ P ⌝ₚ ⟧₅
  explicate-correct  : ∀ (P : Impᵀ.Program) → ⟦ explicate P ⟧ᶜ ≃ ⟦ P ⟧ᵢ
  select-correct     : ∀ (P : CFGᵀ.Program) → ⟦ select P ⟧ₓ ≃ ⟦ P ⟧ᶜ

  -- the whole compiler
  Same : 𝒫 Value → 𝒫 Value → Set          -- as today
  compile-correct     : ∀ (M : ISWIM.AST) → Closed M → Same (⟦ M ⟧ ρ₀) ⟦ compile M ⟧₅
  compile-mon-correct : ∀ (M : ISWIM.AST) → Closed M → Same (⟦ M ⟧ ρ₀) ⟦ ⌜ compile-mon M ⌝ₚ ⟧₅
  compile-imp-correct : … ⟦ compile-imp M ⟧ᵢ    compile-cfg-correct : … ⟦ compile-cfg M ⟧ᶜ
  compile-x86-correct : … ⟦ compile-x86 M ⟧ₓ

  -- adequacy, as today: the ISWIM machine (unchanged), the Clos5ᵀ
  -- machine on compile M (Semantics.CEK.Typed.Clos5, the CEK column's)
  -- and the X86 machine on compile-x86 M (unchanged)
  iswim-error-iff, iswim-const-iff, iswim-converges-iff, iswim-diverges-iff      -- unchanged
  clos5-error-iff     : ∀ (M : ISWIM.AST) → Closed M
    → (ω ∈ ⟦ compile M ⟧₅) ⇔ Terminates (Clos5ᵀₘ.sem (compile M)) o-error
  clos5-const-iff, clos5-converges-iff, clos5-diverges-iff    -- likewise
  x86-error-iff, x86-const-iff, x86-converges-iff, x86-diverges-iff   -- on compile-x86 M
  end-to-end-error / -const / -converges / -diverges, and the -x86 ones   -- as today

-}

module proof.Spec.Typed.GraphErrors where
