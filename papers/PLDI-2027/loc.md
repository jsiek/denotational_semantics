# Size of the three compiler-correctness proofs

All three proofs establish end-to-end correctness for the same compiler, `compile`, which runs
ISWIM --enclose--> Clos2 --optimize--> Clos2 --concretize--> Clos3 --delay--> Clos4 --globalize--> Clos5.
Each also proves four more passes, after Essentials of Compilation, and the compilers that extend `compile` with them, end to end: remove complex operands (rco, Clos5 --rco--> Clos5, into monadic normal form; `compile-mon`, see [Remove complex operands](#remove-complex-operands)), lift locals (monadic Clos5 --lift--> Imp, an imperative language with frames of mutable slots; `compile-imp`, see [Lift locals](#lift-locals)) and explicate control (Imp --explicate--> CFG, a C-like language of blocks; `compile-cfg`, see [Explicate control](#explicate-control)) and select instructions (CFG --select--> X86, x86 with variables over abstract values; `compile-x86` = select ∘ `compile-cfg`, see [Select instructions](#select-instructions)).

* **Denotational:** a graph-model semantics for each language and one correctness proof per pass, in `agda/Compiler/Model/Graph/`, over the graph model in `agda/GraphModel/`. The theorem is `CompilerCorrect`: the source and compiled program produce the same constants, and one denotation is nonempty exactly when the other is.
* **CompCert-style:** a small-step CEK machine for each language and one forward simulation per pass, in `agda/Compiler/Operational/`. The theorem is `CompilerSim`: the two programs terminate with the same observation, including going wrong, and one diverges exactly when the other does.
* **CakeML-style:** a functional big-step semantics with a clock for each language (a total interpreter that ticks the clock at each function call and times out when it runs out) and one clock-for-clock proof per pass, in `agda/Compiler/Functional/`. The theorem is `CompilerFuel`. It has the same shape as the CompCert-style one, over the same observations: a program terminates with o if it does so for some clock, and diverges if it times out for every clock. The interpreters are written in Agda's do-notation, which desugars to the same binds `_>>=_` of the result monad.

Counts are code lines: lines that are neither blank nor comments. The tables are regenerated with
`python3 papers/PLDI-2027/loc.py` from the repository root. The script fails if any Agda module is not assigned to a group, if one proof imports another proof's modules, adequacy's or an experiment's, or if a module of the language-independent infrastructure imports anything that is not infrastructure.

**How totals are computed.** Each module belongs to one group: one of the three proofs, adequacy, shared, language-independent infrastructure, examples, or an experiment. A proof's total is its own modules plus every shared module that it imports, directly or transitively, *unless all three proofs import it*. So each column is the standalone size of that proof, apart from two things. What is common to all three proofs: the languages, the compiler passes and `compile` (`Compiler/Compile/Pipeline.agda`). And the language-independent infrastructure, code that other languages and compilers would reuse unchanged (the abt library and syntax lemmas, the denotational framework and the graph model, the small-step and clocked frameworks; see [Language-independent infrastructure](#language-independent-infrastructure)). Neither is counted in any column; the infrastructure has its own table, which shows what each proof relies on. A shared module that only some proofs use is counted in each of them; it is the row "shared modules not used by all three proofs", listed [below](#shared-modules). Examples are not counted. Adequacy is reported separately (see below). The import graph is read from the `import` and `open import` lines.

## Current counts

As of this PR:

| component | denotational | CompCert-style | CakeML-style |
|---|---:|---:|---:|
| semantics of the languages | 845 | 756 | 561 |
| enclose | 102 | 222 | 162 |
| optimize | 156 | 273 | 194 |
| concretize | 246 | 218 | 152 |
| delay | 846 | 168 | 116 |
| globalize | 243 | 189 | 134 |
| rco | 243 | 449 | 298 |
| lift locals | 275 | 218 | 143 |
| explicate control | 210 | 152 | 145 |
| select instructions | 322 | 272 | 140 |
| composition | 49 | 32 | 37 |
| shared modules not used by all three proofs | — | 379 | 379 |
| **total** | **3537** | **3328** | **2461** |

The denotational lift-locals and explicate-control rows are the proofs against the continuation-passing semantics of Imp; the proofs against the direct semantics are an experiment (see [Explicate control](#explicate-control)).

Language-independent infrastructure, not in any total (see [Language-independent infrastructure](#language-independent-infrastructure)); each proof column is the part of a group that the proof reaches:

| language-independent infrastructure (not in the totals) | lines | used by denotational | used by CompCert-style | used by CakeML-style |
|---|---:|---:|---:|---:|
| abstract binding trees | 220 | 220 | 220 | 220 |
| syntax lemmas (renaming, scoping, uses), list lookups | 273 | 212 | 273 | 273 |
| base types, logical equivalence | 26 | 22 | 26 | 26 |
| denotational framework | 395 | 395 | — | — |
| graph model: values, operators, continuity | 512 | 512 | — | — |
| small-step framework: transition systems, simulations | 187 | — | 187 | — |
| clocked big-step framework | 80 | — | — | 80 |
| **total** | **1693** | **1361** | **706** | **599** |

Adequacy uses 1519 lines of the infrastructure, 158 of them not used by the denotational proof.

Adequacy relates the denotational semantics of ISWIM, Clos5 and X86 to their machines. It turns `CompilerCorrect`, and the end-to-end theorem for the whole compiler, `compile-x86` (`SelectCorrect`), into statements about running programs (`Adequacy/EndToEnd.agda`; see [Adequacy for X86](#adequacy-for-x86)). It is reported separately, because the denotational semantics can be taken as *the* semantics of a language, in which case adequacy is not needed. It is an add-on to the denotational proof, so its total also counts the shared modules it imports that the denotational total does not already count (the observations, closedness, the scoping of `compile`'s output and growing tables, 379 lines); the denotational total plus the adequacy total is then standalone, except for the infrastructure and for the ISWIM, Clos5, Imp and X86 machines (418 lines, plus the 3-line instance of the small-step framework; X86's frames are Imp's), which adequacy reuses from the CompCert-style proof and which are not counted again.

| adequacy (denotational side only) | lines |
|---|---:|
| ISWIM | 855 |
| Clos5 | 863 |
| X86 | 1243 |
| well-formedness of compiled programs | 328 |
| end to end | 39 |
| shared modules not used by all three proofs, nor by the denotational one | 379 |
| **total** | **3707** |

Two experiments, not in the totals: a direct backward simulation for delay, described [below](#experiment-a-direct-backward-simulation-for-delay), and the direct denotational semantics of Imp with lift locals and explicate control proved against it, described in [Explicate control](#explicate-control). The direct proofs also use `Sem/Imp.agda`, `LiftLocalsCommon` and `ExplicateCommon`, which are counted in the main rows.

| experiment (not in the totals) | lines |
|---|---:|
| CompCert-style: direct backward simulation for delay — framework | 94 |
| CompCert-style: direct backward simulation for delay — delay | 149 |
| denotational: direct Imp — semantics | 38 |
| denotational: direct Imp — lift locals | 108 |
| denotational: direct Imp — explicate control | 559 |

### Shared modules

| shared module | lines | used by |
|---|---:|---|
| `Compiler.Compile.Concretize` | 57 | all three proofs |
| `Compiler.Compile.Delay` | 32 | all three proofs |
| `Compiler.Compile.Enclose` | 33 | all three proofs |
| `Compiler.Compile.EncloseScope` | 55 | CompCert-style, CakeML-style, adequacy |
| `Compiler.Compile.Explicate` | 37 | all three proofs |
| `Compiler.Compile.Globalize` | 52 | all three proofs |
| `Compiler.Compile.GlobalizeTable` | 52 | CompCert-style, CakeML-style, adequacy |
| `Compiler.Compile.LiftLocals` | 44 | all three proofs |
| `Compiler.Compile.Optimize` | 62 | all three proofs |
| `Compiler.Compile.Pipeline` | 28 | all three proofs |
| `Compiler.Compile.PipelineScope` | 249 | CompCert-style, CakeML-style, adequacy |
| `Compiler.Compile.RCO` | 120 | all three proofs |
| `Compiler.Compile.Select` | 39 | all three proofs |
| `Compiler.Lang.CFG` | 28 | all three proofs |
| `Compiler.Lang.Clos2` | 39 | all three proofs |
| `Compiler.Lang.Clos3` | 39 | all three proofs |
| `Compiler.Lang.Clos4` | 53 | all three proofs |
| `Compiler.Lang.Clos5` | 62 | all three proofs |
| `Compiler.Lang.ISWIM` | 39 | all three proofs |
| `Compiler.Lang.Imp` | 37 | all three proofs |
| `Compiler.Lang.Mon` | 52 | all three proofs |
| `Compiler.Lang.Prim` | 13 | all three proofs |
| `Compiler.Lang.X86` | 49 | all three proofs |
| `Compiler.Observation` | 23 | CompCert-style, CakeML-style, adequacy |

Shared by all three proofs, and not counted: 20 modules, 915 lines. Counted in both operational totals and in adequacy: `Compile.EncloseScope` (55), `Compile.GlobalizeTable` (52), `Compile.PipelineScope` (249) and `Observation` (23), 379 lines. The denotational total counts no shared module. Examples, not counted: 282 lines.

### Infrastructure modules

| infrastructure module | lines | used by |
|---|---:|---|
| `Clocked` | 80 | CakeML-style |
| `GraphModel.Continuity` | 166 | denotational, adequacy |
| `GraphModel.Domain` | 84 | denotational, adequacy |
| `GraphModel.Ops` | 230 | denotational, adequacy |
| `GraphModel.SemanticsUtil` | 32 | denotational, adequacy |
| `Iff` | 4 | CompCert-style, CakeML-style, adequacy |
| `ListUtil` | 92 | denotational, CompCert-style, CakeML-style, adequacy |
| `NewDOpSig` | 35 | denotational, adequacy |
| `NewDenotProperties` | 16 | denotational, adequacy |
| `NewEnv` | 99 | denotational, adequacy |
| `NewSemantics` | 99 | denotational, adequacy |
| `NewSigUtil` | 6 | denotational, CompCert-style, CakeML-style, adequacy |
| `NewSyntaxUtil` | 9 | denotational, CompCert-style, CakeML-style, adequacy |
| `Primitives` | 22 | denotational, CompCert-style, CakeML-style, adequacy |
| `RenameSem` | 60 | denotational, adequacy |
| `SetsAsPredicates` | 58 | denotational, adequacy |
| `Simulation` | 94 | CompCert-style |
| `Smallstep` | 93 | CompCert-style, adequacy |
| `Syntax.Rename` | 65 | denotational, CompCert-style, CakeML-style, adequacy |
| `Syntax.Scope` | 32 | CompCert-style, CakeML-style, adequacy |
| `Syntax.ScopeRename` | 29 | CompCert-style, CakeML-style, adequacy |
| `Syntax.Uses` | 55 | denotational, CompCert-style, CakeML-style, adequacy |
| `abt.AbstractBindingTree` | 18 | denotational, CompCert-style, CakeML-style, adequacy |
| `abt.Fold2` | 28 | denotational, adequacy |
| `abt.GSubst` | 9 | denotational, CompCert-style, CakeML-style, adequacy |
| `abt.ScopedTuple` | 137 | denotational, CompCert-style, CakeML-style, adequacy |
| `abt.Sig` | 18 | denotational, CompCert-style, CakeML-style, adequacy |
| `abt.Var` | 23 | denotational, CompCert-style, CakeML-style, adequacy |

## What the groups contain

* **shared (counted only in the proofs that use it when not all three do, see above):** the languages (Imp's expressions without control flow are `Simple`, in `Lang/Imp.agda`, shared with `Lang/CFG.agda`), the compiler passes and their compositions `compile`, `compile-mon`, `compile-imp`, `compile-cfg` and `compile-x86` (`Compile/Pipeline.agda`), which all three proofs use; the observations and the end-theorem shape (`Compiler/Observation.agda`); and the lemmas about the compiler's output that both operational styles use:
  * `Compile/EncloseScope.agda`: closed ISWIM programs and `enclose-closed` (from `EncloseSim` and `OptimizeSim`);
  * `Compile/GlobalizeTable.agda`: growing tables `_⊑_`, `glob-grows` and `global-⊑` (from `GlobalizeSim`); the table lookup `global` itself moved to `Lang/Clos5.agda`, so the machine and the interpreter use the same one;
  * `Compile/PipelineScope.agda`: well-scoped Clos5 programs (`Scoped`, the precondition of both operational rco proofs) and `compile-scoped`, that `compile` produces them from closed ISWIM programs, one lemma per pass (formerly the well-scopedness half of adequacy's `CompileWF`). Only the end-to-end `compile-mon` theorems of the operational proofs use it (and, through them, those of `compile-imp`, `compile-cfg` and `compile-x86`).
* **language-independent infrastructure (not counted):** see [Language-independent infrastructure](#language-independent-infrastructure).
  * the abt library, `NewSigUtil`, `NewSyntaxUtil`;
  * `Syntax/`: the lemmas about the syntax of any signature, `Rename.agda` (`rename-cong`, `rename-fuse`, `rename-id`, from `DelaySim`), `Scope.agda` (well-scoped terms and `ws-uses`, from `OptimizeSim`), `ScopeRename.agda` (renaming preserves well-scopedness, formerly adequacy's `Scope`), `Uses.agda`; and `ListUtil.agda`, lookup in an environment, projection from a tuple, and lemmas about lookups, also in reversed and replicated lists (formerly `Operational/Machine/Common.agda`, plus list lemmas from `ConcretizeSim` and `GlobalizeSim`, and from adequacy);
  * `Primitives.agda` (base types) and `Iff.agda` (`_⇔_`);
  * the denotational framework: sets as predicates, environments, the semantics of any signature and its monotonicity (`NewSemantics`, which also gives consistency), DOp signatures, `abt.Fold2`, `RenameSem`;
  * the graph model, `GraphModel/`: values and consistency (`Domain`), the semantic operators with their monotonicity and consistency (`Ops`), their continuity (`Continuity`), and continuity of semantics in the environment (`SemanticsUtil`, formerly `Sem/Continuous`);
  * the small-step framework (`Smallstep.agda`, `Simulation.agda`: transition systems, forward simulation, backward from forward plus determinism, the iff end theorem) and the clocked one (`Clocked.agda`: results with timeout, the clocked end theorem, `clocked`), both parameterized over the type of observations.
* **semantics of the languages:**
  * denotational: the meaning of this compiler's primitives (`Model/Graph/Prim.agda`: `out`, `primD` and its lemmas), the semantics of ISWIM, Clos2 through Clos5, Imp, CFG and X86, plus the continuity instances the proofs use (for Clos5, `Sem/Clos5IswimContinuous.agda`, used by rco, lift locals and adequacy). For Imp: `Sem/Imp.agda` (stores, slots, the frame check, atoms, simple expressions, frames and tables, also used by CFG and by the direct semantics) and the continuation-passing semantics `Sem/ImpK.agda`; the direct one, `Sem/ImpDirect.agda`, is an experiment;
  * CompCert-style: the eight machines (ISWIM, Clos2–Clos5, Imp, CFG and X86), and the small-step framework at this compiler's observations (`Operational/Smallstep.agda`, `Operational/Simulation.agda`, which keep the design notes);
  * CakeML-style: the eight clocked interpreters (Clos5's, Imp's, CFG's and X86's take the table of global definitions), and the clocked framework at this compiler's observations (`Functional/Clock.agda`).
* **one row per pass:** that pass's correctness proof. The rco row also contains the end-to-end theorem for `compile-mon`, a corollary of the composition and the rco theorem (11 lines in the denotational proof, 2 in each operational one), in all three styles; likewise the lift-locals row contains the end-to-end theorem for `compile-imp`, the explicate-control row the one for `compile-cfg`, and the select-instructions row the one for `compile-x86`. The denotational lift-locals and explicate-control rows include the modules both semantics of Imp use (`LiftLocalsCommon`, `ExplicateCommon`).
* **composition:** the end-to-end theorem built from the per-pass results. The compiler `compile` itself is shared (`Compile/Pipeline.agda`), so neither operational proof imports the denotational one.
* **shared modules not used by all three proofs:** see [Shared modules](#shared-modules).

## Caveats

* **The theorems differ.** The CompCert-style and CakeML-style theorems have the same shape. They are stronger than the denotational one: it separates going wrong from divergence. In the graph model, both denote ∅.
* **Determinism.** The CompCert-style proof relies on every machine being deterministic and total. The backward direction of each pass comes from forward simulation plus determinism, and the framework proves that once. The CakeML-style proof needs no determinism argument: an interpreter is a function, and every pass is proved clock for clock (see below).
* **Why "backward = forward + determinism" has no denotational counterpart.** Consistency of denotations plays the role of determinism. Take c ∈ ⟦pass M⟧ and suppose ⟦M⟧ has an element.
  * If it is a constant c′, the forward direction puts c′ in ⟦pass M⟧, and consistency forces c = c′.
  * If it is a function, tuple or sum, consistency rules out c.

  That leaves ⟦M⟧ = ∅, and showing that ⟦pass M⟧ = ∅ too is a reflection argument. A forward relation cannot carry absence.

  This is inherent in a continuous semantics. Every element of a denotation is a finite observation, evidence available after finitely much computation. Termination with a result is a finite observation; divergence is not, since no finite evidence shows that a program diverges. So divergence can only appear as the absence of elements, and an element marking divergence would make the semantics non-monotone. The CompCert-style proof avoids this because its divergence is an infinite run, a coinductive object that forward simulation maps to another infinite run.

  Adding an error element for stuck programs would not change this. It would make going wrong a finite observation, handled by the forward direction plus consistency, but ∅ would still mean divergence and would still have to be reflected. Avoiding the reflection would take a coinductive semantics, such as the delay monad or traces, and that gives up the finite-observation style.

  The cost falls only on passes that change representation. When ⟦pass M⟧ ≃ ⟦M⟧ (enclose, optimize, concretize, globalize, rco, lift locals, explicate control), both directions come from the equation at once, with no determinism argument.
* **Machines.** The ISWIM, Clos2 and Clos3 machines check that an operator is a function before evaluating the argument. Delay needs this to preserve going wrong: it takes the closure apart with `fst` before the argument. The Clos4 and Clos5 machines check that the operator is code only at the call, after all three operands, like an indirect call instruction, so that rco, which let-binds all the operands before the call, preserves going wrong. On delay's output the late check always passes, since a non-closure has already gone wrong at `fst`.

* **Binders bind only consistent sets.** In the graph model, Λ and 𝒞 bind only finite sets that are consistent, so a denotation under a consistent environment has no inconsistent elements. This was needed for explicate control: with binders that admit any finite set, ⟦explicate P⟧ ≃ ⟦P⟧ is false (see [Explicate control](#explicate-control)). It cost 96 denotational lines and 74 adequacy lines when it was made, and saved 16 in delay, whose own consistency induction gave way to a generic one: the monotonicity proof of the denotational framework now works for any relation the operators preserve, so the consistency of each semantics comes from its operator lemmas. Where a proof picks a finite part of a set for a binder (concretize, delay in both directions, rco's let-β), it needs that set consistent, so those proofs take a consistent environment.
* **Two denotational semantics of Imp.** The main rows use a continuation-passing semantics of Imp (`Sem/ImpK.agda`); a direct one (`Sem/ImpDirect.agda`), with lift locals and explicate control proved against it, is kept as an experiment. Choosing the semantics is part of the proof effort, as choosing the machines or interpreters is for the operational styles; the CPS one is the better effort for this pass sequence. See [Explicate control](#explicate-control).
* **Clos5 continuity is denotational.** The continuity of the Clos5 semantics in the environment (117 lines then, 157 now), formerly adequacy's `Clos5Continuous`, is now `Model/Graph/Sem/Clos5IswimContinuous.agda`, in the denotational row "semantics of the languages", because the rco proof uses it (for the let laws), as does lift locals. Adequacy reuses it from there and does not count it again; adequacy's Clos5 row shrank by the same 117 lines.
* **The rco preconditions differ.** The denotational rco theorem is an equation with no precondition on programs; both operational ones need `Scoped`, and their end-to-end `compile-mon` theorems therefore pay for `compile-scoped` (249 lines, in the shared row, plus `Syntax/ScopeRename`, now infrastructure). See [Remove complex operands](#remove-complex-operands).
* **Lift locals and explicate control need no precondition in any style.** A variable out of scope becomes a slot beyond the frame, which goes wrong (operationally) or reads as `init` (denotationally) exactly where the Clos5 variable does. Assigning a slot beyond the frame goes wrong in all three styles (∅ denotationally, since explicate control; see [Explicate control](#explicate-control)). See [Lift locals](#lift-locals).
* **Select instructions: a precondition only in the denotational proof.** The denotational theorem assumes every global definition has at least 2 locals (`select-correct`), discharged for compiled programs; neither operational one has a precondition. See [Select instructions](#select-instructions).
* **Adequacy reaches X86, the final target, but not the intermediate languages.** Adequacy, and so a statement about running code, exists for ISWIM, Clos5 and X86: the end-to-end theorem for `compile-x86` relates the ISWIM machine to the X86 machine (`end-to-end-x86-const`, `end-to-end-x86-converges`). The end-to-end denotational theorems for `compile-mon`, `compile-imp` and `compile-cfg` still speak only about the denotations of Clos5, Imp and CFG. X86 adequacy has preconditions that compiled programs satisfy, discharged by `compile-x86-wf` (see [Adequacy for X86](#adequacy-for-x86)); like Clos5's, it cannot tell going wrong from diverging.

## History

| date | change | denotational | CompCert-style | CakeML-style |
|---|---|---:|---:|---:|
| 2026-10-11 | first complete versions (PR #14) | 4251 | 2134 | — |
| 2026-10-11 | leaner delay proof (PR #15) | 3725 | 2134 | — |
| 2026-10-11 | dead code, consistency, shared lemmas (PR #16) | 2836 | 2134 | — |
| 2026-10-11 | delay relation without visible fuel, Calls as a predicate (PR #17) | 2825 | 2134 | — |
| 2026-10-11 | joined pairs ⦅ u , v ⦆ instead of the halves ⦅ u ∣ and ∣ v ⦆ (PR #18) | 2823 | 2134 | — |
| 2026-10-11 | CompCert-style cleanup: framework specialised to step-function machines, end theorems composed instead of simulations, no per-pass corollaries, shared `uses-bound`, pruned imports (PR #20) | 2811 | 1862 | — |
| 2026-10-11 | CakeML-style pilot: clocked interpreters for all five languages, enclose clock for clock | 2811 | 1862 | 541 |
| 2026-10-11 | CakeML-style complete: all five passes clock for clock, composition (`CompilerFuel`); machine-independent lemmas and observations moved to shared modules, so neither operational style imports the other (PR #21) | 2811 | 1626 | 1130 |
| 2026-10-11 | `compile` moved from `CompilerCorrect` to the shared `Compile/Pipeline.agda`, so no operational proof imports the denotational one; dead imports of the denotational infrastructure removed from the languages (PR #24; old method) | 2804 | 1626 | 1130 |
| 2026-10-11 | the same code, new method: shared modules not used by all three proofs counted in each proof that uses them (PR #24) | 2832 | 1783 | 1287 |
| 2026-10-11 | arithmetic: sub and eq (PR #25) | 2935 | 1933 | 1407 |
| 2026-10-11 | late code check in Clos4/Clos5 (PR #26) | 2935 | 1926 | 1404 |
| 2026-10-11 | remove complex operands, all three proofs; Clos5 continuity to the denotational side, scoping of `compile` to the shared code (PR #26) | 3289 (+354) | 2653 (+727) | 1980 (+576) |
| 2026-10-12 | lift locals into Imp, all three proofs (PR #27) | 3551 (+262) | 2967 (+314) | 2184 (+204) |
| 2026-10-12 | explicate control into CFG, all three proofs, the denotational one against the direct semantics of Imp; binders bind only consistent sets (PR #28) | 4323 (+772) | 3181 (+214) | 2365 (+181) |
| 2026-10-12 | continuation-passing semantics of Imp for the denotational lift locals and explicate control, the direct one an experiment; what both have in common factored out (PR #28) | 3989 (−334) | 3181 | 2365 |
| 2026-10-12 | the same code, new method: language-independent infrastructure in a separate table, not counted (PR #28) | 3113 | 2935 | 2224 |
| 2026-10-12 | select instructions, all three proofs (PR #29) | 3537 (+424) | 3325 (+390) | 2463 (+239) |
| 2026-10-12 | CakeML-style interpreters in do-notation (cosmetic; PR #30) | 3537 | 3325 | 2463 |
| 2026-10-12 | X86 machine and interpreter aligned with the X86 semantics at calls; adequacy for X86, end to end for `compile-x86` (this PR) | 3537 | 3328 (+3) | 2461 (−2) |

**Adequacy for X86 (this PR).** The X86 machine and interpreter now do what the X86 semantics says at calls (see [Select instructions](#select-instructions)): the callee starts with `%rax` unset and no flag, `callq` goes wrong if `%rdi` or `%rsi` is unset, and `retq` goes wrong if `%rax` is unset, also when it returns to a caller. This cost the CompCert-style semantics 3 lines (the machine) and saved the CakeML-style select proof 2 (its hypothesis on calls lost the registers); `SelectSim` and `SelectFuel` still need no precondition. Adequacy went from 2187 to 3707 lines: X86 +1243, well-formedness 60 → 328, end to end 24 → 39, ISWIM +2 and Clos5 −8 (the runs of any machine are now shared, `Common.Runs`, and the Clos5 machine's values, which X86 shares, are in `Values.agda`, used by both); the list lemmas it needed went to `ListUtil` (infrastructure, 62 → 92 lines, also used by Clos5 adequacy).

The last two PR #28 rows are, apart from moving modules, the same code counted two ways. The infrastructure was split from the compiler (the graph model's values, consistency and operators from `Compiler/Model/Graph/Domain/ISWIM/` to `GraphModel/`, leaving only the meaning of the primitives, `Compiler/Model/Graph/Prim.agda`; `Sem/Continuous` to `GraphModel/SemanticsUtil`, `Sem/RenameSem` to `RenameSem`; the syntax lemmas from `Compiler/Lang` to `Syntax/`; the small-step and clocked frameworks parameterized over the type of observations, with instances at this compiler's observations left in `Compiler/`), and the infrastructure left the totals. The rows "generic infrastructure" (307, 188, 80) and "domain, operators, continuity" (511, denotational only) are gone, and so are the shared modules that became infrastructure (`abt.Fold2`, 28, from the denotational total; `Syntax.Scope` and `Syntax.ScopeRename`, 61, from both operational totals); `Observation` shrank from 26 to 23 lines (`_⇔_` to `Iff`, `SameObs` unfolded in the frameworks). The semantics rows went from 782, 629, 461 to 743, 635, 464 (the denotational one gaining `Prim.agda`, the operational ones the instances of their frameworks), and the denotational pass rows changed by 1 to 3 lines each (imports). In all −876, −246 and −141. What each proof relies on now appears in the infrastructure table (1331, 676 and 569 lines). Adequacy went from 2172 to 2246 with the consistent binders (ISWIM 798 → 850, Clos5 847 → 869), and from 2246 to 2187 with the new method (ISWIM 853, Clos5 871, shared 443 → 379).

The two PR #24 rows are the same code counted two ways. Before, every shared module was left out of all totals, although four of them (157 lines) are used only by the two operational proofs and adequacy, and one (`abt.Fold2`, 28 lines) only by the denotational proof and adequacy; now these count in each proof that uses them (+28, +157, +157), and adequacy grows from 1981 to 2138. Moving `compile` took 7 lines from the denotational composition (the definitions and their imports); the shared code went from 1071 to 1069 lines (+13 for `Pipeline`, −15 for the dead imports).

PR #16 also changed the grouping: the shared counts now include `Primitives`, `NewSigUtil` and `NewSyntaxUtil`, and `ISWIMContinuous` moved to adequacy. Earlier rows used slightly different groups, so they are only roughly comparable. The PR #21 row moved 236 lines from the CompCert-style column to the shared code (net, per row: generic infrastructure −21 for the observations, machines −49 for the list lookups, optimize −62 and enclose −1 for well-scopedness and closedness, concretize −13 and globalize −44 for list and table lemmas, delay −47 for the renaming lemmas, composition +1); the shared code grew from 805 to 1071 lines, and adequacy shrank by 7 because its `Scope` now reuses the shared well-scopedness; before it, the CakeML-style column imported those lemmas from the CompCert-style modules and was undercounted (1099 lines with four passes done, against 1130 with all five and the composition).

**Adding a feature: arithmetic (PR #25).** Every language got one operator `prim p ⦅ L , M ⦆`, for p ∈ {sub, eq} on integers, which evaluates both operands left to right and goes wrong unless both are integers. `eq` returns `inl ⟨⟩` for true and `inr ⟨⟩` for false, so `case` serves as `if`. Every pass maps over it. The code shared by all three proofs grew by 34 lines (the languages 15, the passes 6, and `Lang/Prim`, 13). The proofs grew as follows:

| component | denotational | CompCert-style | CakeML-style |
|---|---:|---:|---:|
| domain, operators, continuity | +31 | — | — |
| semantics of the languages | +16 | +65 | +54 |
| enclose | +3 | +16 | +13 |
| optimize | +3 | +16 | +13 |
| concretize | +8 | +13 | +10 |
| delay | +35 | +17 | +11 |
| globalize | +7 | +15 | +11 |
| composition | 0 | 0 | 0 |
| shared modules not used by all three proofs | 0 | +8 | +8 |
| **total** | **+103** | **+150** | **+120** |

* **Denotational.** One semantic operator, `primD p D E = { out (δ p n m) | const n ∈ D, const m ∈ E }`, with its monotonicity, consistency and continuity (+31), one clause per semantics, and a congruence case per pass (`primD-≃`). The exception is delay (+35). Its relations treat flat values (constants, ω, ⟨⟩) as first-order data that need no reflection, and the results `left ⟨⟩` and `right ⟨⟩` of `eq` are not flat. So `Flat` became `Data` (flat values under `left` and `right`) in both directions, and reflect recovers the operands' constants.
* **CompCert-style.** Each machine gets two frames (`primL`, `primR`), three transitions and the value of a result (13 lines per machine). Each simulation relates the two frames and gets three cases and the lemma `prim≈` (related operands give related results, through `obs≈`, 6 lines).
* **CakeML-style.** Each interpreter gets one clause and the value of a result (about 11 lines). Each pass gets one `run≈` case and the same `prim≈`.
* **Shared by the operational proofs:** `δ?`, which applies a primitive to two integer observations (`Observation`, +5), and the new cases of `enclose-ws` and `glob-grows` (+3).
* **Adequacy (+110):** ISWIM +49, Clos5 +48, well-formedness +5, shared +8. Soundness interprets the two frames with `primD`. The step that applies a primitive stays in `primD`, because a primitive is defined only on two integer observations (`δ?-inv`).

**Late code check in Clos4 and Clos5 (PR #26).** The Clos4 and Clos5 machines and interpreters now check that the operator of `app ⦅ L , M , N ⦆` is code at the call, after evaluating all three operands, instead of right after L; ISWIM, Clos2 and Clos3 keep the early check. This is what rco needs to preserve going wrong (see [Caveats](#caveats)). The denotational proof is unchanged. Per module:

| module | before | after | change |
|---|---:|---:|---:|
| machines: Clos4, Clos5 | 103, 107 | 102, 106 | −2 |
| interpreters: Clos4, Clos5 | 78, 81 | 78, 82 | +1 |
| `DelaySim`, `DelayFuel`, `DelayBackSim` (experiment) | 168, 116, 149 | 168, 116, 149 | 0 |
| `GlobalizeSim` | 194 | 189 | −5 |
| `GlobalizeFuel` | 138 | 134 | −4 |
| adequacy: `Clos5Soundness` | 446 | 436 | −10 |
| adequacy: `Clos5LogRel` | 268 | 268 | 0 |

* **Delay** needs no change in either style: Clos3's closure check is matched by Clos4's `fst` of the let-bound closure, as before, and the late code check passes on delay's output in the same number of steps.
* **Globalize** compares two late checks. `GlobalizeSim` loses the five stuck cases at `appF`. In `GlobalizeFuel` the case split on the operator moves from `apply≈` to `call≈`, which no longer needs a local lemma for the clock.
* **Clos5 soundness** loses the stuck cases at `appF` in `step-⊆` and `halts` (five each).
* **Interpreters.** Clos4's `call` takes the operator value and goes wrong on a non-code one; Clos5's `apply` passes `code? f` (the definition, if `f` is a code pointer) to its existing `call`.

**Remove complex operands (PR #26).** The new rows, and what moved:

| component | denotational | CompCert-style | CakeML-style |
|---|---:|---:|---:|
| semantics of the languages | +117 | 0 | 0 |
| rco | +237 | +449 | +298 |
| shared modules not used by all three proofs | 0 | +278 | +278 |
| **total** | **+354** | **+727** | **+576** |

The +117 is `Clos5IswimContinuous`, moved from adequacy; the +278 are `PipelineScope` and `ScopeRename`, the scoping of `compile`'s output, moved from adequacy's well-formedness and split from its RB half. Adequacy went from 2238 to 2172 lines: Clos5 −117, well-formedness 287 → 60, shared +278 (the split costs 51 lines: `CompileWF` now proves only that each definition refers to older ones, `glob-rb`, and pairs it with `compile-scoped`).

**Explicate control and consistent binders (PR #28).** The first of the three rows of PR #28, by row (old method):

| component | denotational | CompCert-style | CakeML-style |
|---|---:|---:|---:|
| generic infrastructure | +4 | 0 | 0 |
| domain, operators, continuity | +29 | — | — |
| semantics of the languages | +113 | +62 | +36 |
| concretize | +3 | 0 | 0 |
| delay | −16 | 0 | 0 |
| rco | +5 | 0 | 0 |
| explicate control | +634 | +152 | +145 |
| **total** | **+772** | **+214** | **+181** |

* **Explicate control.** The CFG machine (50) and interpreter (32), and the factoring of the Imp machine (+12) and interpreter (+4) that they share; the denotational semantics of CFG with the factoring of simple expressions in `Sem/Imp.agda` (+42); the three proofs (634, 152, 145).
* **Consistent binders** (denotational +96, adequacy +74): the rest of the denotational rows (+4, +29, +71 of the semantics, +3, −16, +5), and adequacy's ISWIM (+52) and Clos5 (+22).

The second row (−334) replaced the direct semantics of Imp by the continuation-passing one in the main rows: lift locals 186 → 274, explicate control 634 → 210, semantics +2; the direct semantics and its two proofs (then 38, 107 and 558 lines, with the common modules factored out) became an experiment. The third row is the change of method explained above.

## Remove complex operands

The pass (`Compile/RCO.agda`, Clos5 → Clos5, shared) binds every complex operand of a construct to a fresh variable by a `let`, left to right, and leaves atoms (variables, literals, code pointers) in place, shifted under the new lets; the result is in monadic normal form (`Lang/Mon.agda`). It adds no calls and `let` does not tick. The late code check in the Clos4 and Clos5 machines and interpreters (see [Caveats](#caveats)) was added for this pass: with the check right after the operator, `app ⦅ L , M , N ⦆` with a non-code L goes wrong before M runs, while its rco, `let x = L in let y = M in …`, would run M first.

* **Denotational (237 lines): an exact equation.** `rco-correct : ⟦ rco M ⟧[ T ] ρ ≃ ⟦ M ⟧[ T ] ρ` for nonempty ρ, and `rco-program-correct : ⟦ rco-program P ⟧ₚ ≃ ⟦ P ⟧ₚ` for **every** program, with no scoping precondition. The laws are that `let` is strict and otherwise substitutes the meaning of its right-hand side (`let-strict`, `let-β`, which uses the continuity of Clos5), and that every construct whose operands rco names is a strict congruence (`Strict`); one lemma for the let chain (`lift-≃`) then gives each construct in one line. Order of evaluation is invisible: going wrong and divergence both denote ∅, and an unbound variable denotes {ω}.
* **CompCert-style (449 lines).** A forward simulation of the Clos5 machine by itself, for programs in `Scoped`. The target environment has the values of the lets in front, so terms are related up to a renaming (`Ren`). The source frames of a construct are related to the target's remaining let chain by `Pend` (one constructor per operand: a complex operand runs in lock step under a let frame, an atom is evaluated by the source while the target waits, with a decreasing index, and at the end the target runs the construct on its atoms up to the same final frame, `retT`).
* **CakeML-style (298 lines): clock for clock, with equality of results.** For `Scoped` programs, `eval ds ck ρ M ≡ eval (map rco ds) ck ρ (rco M)` for every clock (`run≈`): values contain no code, so they are equal, not just related. The key lemma is the let chain (`lets≈`): evaluating the chain evaluates the complex operands left to right and then the construct with the atoms bound to their values; renaming commutes with evaluation (`ren`).

**Why the operational proofs need `Scoped`.** An atom left in place is evaluated after the complex operands that follow it. An unbound variable goes wrong when it is evaluated, so it would go wrong later: ``pair (` 0) L`` with L a loop goes wrong in the empty environment, while its rco, ``let x = L in pair (` 1) (` 0)``, diverges. In the denotational semantics both denote ∅, so the equation holds anyway. `Scoped` (main closed, each definition in its two parameters) rules this out; the compiler produces such programs (`compile-scoped`, 249 lines, counted in both operational totals because only their `compile-mon` theorems use it, plus the 29 of `Syntax/ScopeRename`, now infrastructure).

The sizes in this section are as of PR #26 (now 243, 449 and 298).

## Lift locals

The pass (`Compile/LiftLocals.agda`, shared, 44 lines) takes a monadic Clos5 term to Imp (`Lang/Imp.agda`, shared, 35 lines). Imp has no binders: each body declares a frame of slots, a variable names a slot, `let` becomes the assignment `x := e₁; e₂`, and `case` assigns the payload to a slot. The frame is threaded: an assignment is seen by everything that runs after it in the same frame, also after the expression that contains it. A call runs the callee in a fresh frame (free variables in slot 0, argument in slot 1) and leaves the caller's frame as it was; reading or assigning a slot beyond the frame goes wrong. Slots are de Bruijn levels: the variable x at depth d is slot d ∸ (x + 1), and a `let` or `case` at depth d assigns slot d, so code at depth d assigns only slots that no variable in scope names. The frame has d₀ + height slots (height = deepest nesting of binders), and a variable out of scope becomes slot n, beyond the frame. No proof needs a precondition, and the semantics of Imp in each style is new. As of PR #27 (since then, the denotational proof is against a continuation-passing semantics of Imp, and what follows describes the direct one, now an experiment; see [Explicate control](#explicate-control)):

| component | denotational | CompCert-style | CakeML-style |
|---|---:|---:|---:|
| semantics of Imp | +76 | +96 | +61 |
| lift locals | +186 | +218 | +143 |
| **total** | **+262** | **+314** | **+204** |

* **Denotational (76 + 186).** A store σ : ℕ → 𝒫 Value gives each slot a set of values, and an expression means, for the store it enters with, a set of values and the store it leaves (then `Sem/Imp.agda`, now `Sem/ImpDirect.agda`). `x := e₁; e₂` is Clos5's strict let, `⋆ ⟨ Λ F , D₁ ⟩`, applied both to the value and to each slot of the store e₂ leaves (`letₛ`); `case` is `𝒞`, likewise pointwise (`caseₛ`). The slots of a let or case collect only the runs of its body that have a value (`r ↓ y`): a run that goes wrong or diverges leaves no store. Reading or assigning beyond the frame gave `init`, as an out-of-scope variable does in Clos5 (since explicate control, assigning beyond the frame means ∅). The invariant is the operational one, stated pointwise: at depth d the store agrees with ρ, slot d ∸ (x + 1) ≃ ρ x for x < d (`Agree`), and ρ is `init` from d on (`Scope`). The proof (`lift-sem`) shows at once that the value of `lift n d M` is ≃ `⟦ M ⟧ ρ` and that the store it leaves still agrees with ρ when that value is nonempty (`Out`), given `Agree`, `Scope` and `d + height M ≤ n`. Because the conclusion is relative to ρ rather than to the store M started with, coming back from under a binder is `weak` (`Agree (suc d) σ (X • ρ) → Agree d σ ρ`, one line, since `suc d ∸ suc (suc x)` is `d ∸ suc x` by computation), the analogue of the operational `weak`. Each simple construct is one congruence line; let and case reuse rco's `strict-≃`, `⋆-≃`, `Λ-≃` and `𝒞-≃`, and their stores are `out-let` and `out-case`. The nonempty condition is inherent: a stuck case or a let whose right-hand side has no value empties every slot too. No continuity is needed.
* **CompCert-style (96 + 218).** The Imp machine (`Machine/Imp.agda`) carries the frame in its states and evaluates each atom in its own step, through the same continuation frames as the Clos5 machine, plus `assignK`, `caseK` and `callK` (which restores the caller's frame). A frame is related to the environment as `Fr n ρ (ρ ʳ++ τ)`: the environment reversed, then the free slots, n in all, so going under a binder is definitional. Continuations are related by `Kont` (one case per Clos5 frame, plus `weak`, a continuation at depth d is one at depth d + 1, which is where "code at depth d assigns only slots ≥ d" lives, and `call` for `callK`). Every source step is matched by exactly one target step, followed by any `callK` pops (`plus-simulation`, no measure); about half of the 70 lines of `sim` are one-line wrong-value cases.
* **CakeML-style (61 + 143).** The interpreter `eval : ℕ → Frame → Exp → Result (Val × Frame)` ticks only at calls, like Clos5's, so the proof is clock for clock (`sim`), with values related by `≡` (Imp reuses Clos5's values) and frames by the same `Fr n ρ` as the CompCert-style proof.

Unlike rco, the denotational proof is not the smallest here: the store is the new ingredient, and in the graph model it is a second, pointwise output (`Out` and the store halves of `letₛ`/`caseₛ`), while the operational proofs relate whole frames (`ʳ++`). With the invariant stated relative to the environment, as theirs is, the denotational proof is between the two operational ones.

**An experiment: the invariant relative to the environment.** The first version (74 + 204 lines) stated the store conclusion relative to the input store: `Pres d σ r`, the slots below d of the store r leaves are those of σ, as two inclusions, the second only when the value is nonempty, with `pres-refl`, `pres-ext`, `pres-case`, `pres-let`, and `agree-pres` to carry `Agree` across a store that `Pres` relates to the agreeing one (34 lines), and an `Agree` record that read slots through the frame check (needing `read-≃`). The current version (76 + 186) states it relative to ρ, as the operational `Fr n ρ (ρ ʳ++ τ)` does: `Out d ρ r = nonempty (proj₁ r) → Agree d (proj₂ r) ρ`. Then `Pres`, `pres-ext` and `agree-pres` disappear (`weak` is one line), the atomic cases leave the agreement they were given, and `out-case`/`out-let` are one ≃ each instead of two inclusion records. One change to the semantics makes this work: without it, `Out` would need an unconditional ⊆ half besides the conditional ⊇ half (a run of the body with no value still contributes its slots to the let's store), which is `Pres` again; the semantics now gates each run's slots by its value having an element (`_↓_`, 2 lines), which is also the more faithful reading: a run that does not finish leaves no store. Making the store a list, so that agreement is shaped like `ρ ʳ++ τ` and going under a binder is definitional, did not pay off and was not kept: with the function store and de Bruijn levels, `weak` is already definitional, the remaining slot lemmas (`read-at`, `read-out`, `upd-at`, `upd-<`, `slot-<`, 19 lines) have list counterparts of about the same size in the operational proofs (`‼-ʳ++`, `look`, `upd-++`, `assign`), and the pointwise store outputs of `letₛ`/`caseₛ` need a store whose shape does not depend on the run (a function, or a vector indexed by n), not a list. A store output for `letₛ` that is not strict cannot remove the nonempty condition, since a stuck `case` empties the store as well.

## Explicate control

The pass (`Compile/Explicate.agda`, shared, 37 lines) takes Imp to CFG (`Lang/CFG.agda`, shared, 28 lines), a C-like language after Essentials of Compilation. Imp's expressions without control flow became `Simple` (`Lang/Imp.agda`), shared by the two languages. A CFG body has a frame size, a list of blocks and a start. A block is a tail: assignments `x := s` of simple expressions, ending in `return s`, `goto l`, or `case a x l₁ l₂`, which assigns the payload of a to slot x and jumps to l₁ or l₂. Blocks are listed newest first, as Clos5's global definitions are, and a block jumps only to older blocks, so control flow within a body is acyclic: no semantics needs a fixed point over the blocks, and the clocked interpreter does not tick at a goto (it recurses on the list of older blocks). The pass is in continuation-passing style (Danvy): `explicate-assign e x k` translates `x := e` followed by the tail k; a nested assignment `y := e₁; e₂` becomes `y := e₁` followed by `x := e₂` followed by k, and a case gets a join block that holds k, which its branches reach by `goto`, so k is not duplicated. `explicate-tail` translates an expression in tail position. The pass threads the list of blocks, only adding to it, so a tail refers only to blocks made before it.

| component | denotational | CompCert-style | CakeML-style |
|---|---:|---:|---:|
| semantics of CFG | 37 | 50 | 32 |
| explicate control | 210 (106 + 104) | 152 | 145 |

The CFG machine and interpreter reuse the evaluation of simple expressions factored out of the Imp machine (+12 lines there) and interpreter (+4); the denotational CFG semantics reuses `Sem/Imp.agda`. No proof needs a precondition.

* **CompCert-style (50 + 152): a forward simulation with a measure** (`ExplicateSim`). The two machines share the frame and the evaluation of simple expressions and run in lock step except for the control flow that the pass makes explicit. An Imp expression runs as the tail that explicate makes of it in the mode of its continuation: `explicate-tail` in tail position, `explicate-assign e x k` when its value is assigned to x before k runs. So the stack of Imp continuations `x := □; e₂` is a CFG tail (`Ctl`: the tail made of e₂, or a `goto` to the join point that runs it). Imp's step into an assignment `x := e₁; e₂` has no CFG step: e₁ already runs as the tail the assignment runs as. This stutter is measured by the nesting of assignments (`depth`). A value returned to `x := □; e₂` is matched by the assignment and the chain of gotos to join points (`join`), a case by its jump to a block (`Br`). A tail made at the blocks bs runs with any newer blocks (`block-≼`).
* **CakeML-style (32 + 145): clock for clock, with equal results** (`ExplicateFuel`). The pass keeps every call and gotos do not tick, so the interpreters tick in lock step; values are Clos5's in both, and code k names definition k of either program, so results are equal. `Means bs t K`: t, run with any blocks cs ⊒ bs, returns K applied to the frame. The CPS lemma (`assign-ok`): if k means K, `explicate-assign e x k` means running e, assigning its value to x and then K; `explicate-tail e` means the value of e (`tail-ok`); jumps to the join point run k with the blocks it was made with (`jump-at`).
* **Denotational (37 + 210): a congruence** (`ExplicateCommon`, `ExplicateCorrectK`), `explicate-correct : ⟦ explicate P ⟧ₚ ≃ ⟦ P ⟧ᴷₚ` for every program. A CFG tail, given the meanings of the blocks it can see and a store, means a set of values; the blocks of a body get their meanings newest first, as global definitions do, each with the meanings of the older ones, so no fixed point is needed (`Sem/CFG.agda`). Against the continuation-passing semantics of Imp, the tail that `explicate-assign e x k` makes means e run with the continuation that assigns x and runs k, `⟪ explicate-assign e x k ⟫ ≃ ⟦ e ⟧ᴷ (assignK x ⟪ k ⟫)`, and `explicate-tail e` means e run with `halt`. Each case is a congruence: a nested assignment is e₁ with the continuation that assigns y and runs e₂ on both sides, and a case passes the continuation to its branches, which in CFG reach it through the join block. The common module (106) has what the proofs against both Imp semantics share: a tail made at bs means the same with newer blocks (`≼`, `blocks-at`, `goto-≃`, `Stable`), atoms and simple expressions, and the end-to-end theorems `compile-cfg-correct-const` and `-nonempty`.

**The counterexample, and consistent binders.** Explicate control is a commuting conversion: it moves the continuation of an assignment into the branches of a case. With the graph model as it was, where Λ and 𝒞 bind any finite set, the equation ⟦explicate P⟧ ≃ ⟦P⟧ was false, and a machine-checked counterexample showed it (`ExplicateCounterExample`, since removed). Take the Clos5 code `λ fv. λ Y. let y = case Y of inl _ ⇒ ⟨1,1⟩ | inr _ ⇒ ⟨2,2⟩ in ⟨fst y, snd y⟩`, lifted into Imp. The inconsistent argument Y = {left ν, right ν} makes the let bind y to a mix of the two branches, so ⟨1,2⟩ is a result in Imp but not in CFG, where each branch reaches the join point on its own. Such junk entries, elements that no run of a program produces, did not break the equations of the earlier passes; the commuting conversion is where they broke one. The fix was to the domain, not to the pass: Λ and 𝒞 now bind only consistent finite sets, so a denotation under a consistent environment has no inconsistent elements (see [Caveats](#caveats); +96 denotational lines, +74 adequacy, with delay 16 shorter). Separately, assigning beyond the frame in the denotational Imp and CFG now means ∅, as the machines go wrong, instead of `init`, a value after which the program still ran: Imp checks the slot before the right-hand side runs and CFG after, and with `init` the pass could not preserve meanings.

**Two semantics of Imp.** Both are kept. In the direct semantics (`Sem/ImpDirect.agda`, from lift locals), an expression means a set of values and an output store. In the continuation-passing one (`Sem/ImpK.agda`), `⟦ e ⟧ σ κ` runs e in the store σ and gives its value and the store it leaves to the continuation κ, the meaning of the rest of the body; the store is never collected over the runs of an expression. `Sem/Imp.agda` (58) has what both share. With the direct semantics the commuting conversion is in explicate control: in Imp, `x := e; k` runs k in the store e leaves, collected over all runs of e, while in CFG k runs after each run on its own. Each step is a law (`let-assoc`, `let-case`); one direction is monotonicity, the other needs CFG tails to preserve directed unions of stores (`Dir`, `DC`) and the bound sets to be consistent, so that the finitely many runs k used can be merged into one (`merge`), and Imp to be monotone and consistent (`I-mono`, `I-con`). With the continuation-passing semantics, explicate control is the congruence above, and the commuting conversion moves into lift locals, against Clos5: the continuation commutes with let and with case (`let-law`, `case-law`, in `LiftLocalsCorrectK`), two small laws resting on the monotonicity and consistency of Clos5 (`Clos5IswimContinuous`). The chains, with the common modules counted in both denotational rows:

| | semantics of Imp | semantics of CFG | lift locals | explicate control | chain |
|---|---:|---:|---:|---:|---:|
| denotational, continuation-passing (main) | 84 (58 + 26) | 37 | 275 (105 + 170) | 210 (106 + 104) | 606 |
| denotational, direct (experiment) | 96 (58 + 38) | 37 | 213 (105 + 108) | 665 (106 + 559) | 1011 |
| CompCert-style | 108 | 50 | 218 | 152 | 528 |
| CakeML-style | 65 | 32 | 143 | 145 | 385 |

The direct semantics makes lift locals smaller (213 against 275) and explicate control much larger (665 against 210): the store merging, directed continuity over stores, and the monotonicity and consistency of Imp are all in explicate control. With the continuation-passing semantics the denotational chain is 606 lines, against 528 (CompCert-style) and 385 (CakeML-style); with the direct one it is 1011, about twice the CompCert-style chain. The commuting conversion is where the graph model's junk entries broke the equation, and it is where the choice of the semantics of Imp matters most: done against Clos5's binders it costs two small laws, done against stores it costs the bulk of the direct proof.

## Select instructions

The pass (`Compile/Select.agda`, shared, 39 lines) takes CFG to X86 (`Lang/X86.agda`, shared, 49 lines): x86 with variables over **abstract values**, Clos5's, not over a heap. `alloc` and `load` build and take apart objects (tuples, pairs, sums, closures) with no addresses; a concrete heap would be a later pass (expose allocation). The locations are the slots of the frame and the registers `%rax`, `%rdi` and `%rsi`; there is one flag. The instructions are `movq`, `subq`, `cmpq`, `sete`, `testinl`, `alloc`, `load` and `callq`; a block ends in `retq`, `jmp` or `je`, and keeps CFG's label. A call passes the free variables in `%rdi` and the argument in `%rsi` and returns in `%rax`; each definition's prologue moves `%rdi` and `%rsi` to slots 0 and 1, and a call clobbers `%rdi`, `%rsi` and the flag. The callee starts with `%rdi` and `%rsi` as they are and with `%rax` and the flag unset; `callq` reads `%rdi` and `%rsi`, and `retq` reads `%rax`, so each goes wrong on an unset register, in all three semantics (as of this PR; before it, the machine and the interpreter passed the caller's `%rax` and flag to the callee and did not check the registers of a call or a return, which the X86 semantics, strict in them, does). Subtraction goes through `%rax` (two-address `subq`), `eq` is `cmpq; sete`, and `case` is `testinl`, a `load` of the payload and `je`. `compile-x86` is select ∘ `compile-cfg`. Main's frame has `locals` slots, as in CFG: with max(2, locals), as first specified, the end-to-end theorem would be false for open terms whose main reads slot 0 or 1.

| component | denotational | CompCert-style | CakeML-style |
|---|---:|---:|---:|
| semantics of X86 | 102 | 121 | 97 |
| select instructions | 322 | 272 | 140 |
| **total** | **424** | **393** | **237** |

* **CakeML-style (97 + 140): clock for clock, with equal results** (`SelectFuel`), no precondition. Only `callq` ticks, and jumps recurse on the list of older blocks, as in the CFG interpreter. The interpreter runs a block's instructions in continuation-passing style, so the instructions select emits for a CFG statement unfold definitionally to that statement's step.
* **CompCert-style (121 + 272): a forward simulation** (`SelectSim`), no precondition. The X86 machine takes one instruction per step. The simulation runs from synchronisation points, each with a script (`Fate`) of how the two machines reach the next one: both stop (`stop`), the CFG steps while X86 waits (`lag`, measured by the length of the rest of the script), or the CFG steps and X86 takes one or more steps (`go`). Most of the cost is the timing of errors: each X86 instruction must go wrong at the same CFG step that checks the same thing, and the operands of a call are read in a different order (X86 reads f last).
* **Denotational (102 + 322)** (`Sem/X86.agda`, `SelectCorrect`): a continuation-passing semantics, as for Imp. Slot writes are strict, as CFG's `seq`; registers and the flag are written under a nonemptiness guard, so a failing or diverging instruction stops everything after it. (A first version let a register hold a failed value that a later write could forget; the guard cost +6 lines of semantics and +41 of proof. A guard rather than binding with ⋆⟨Λ…⟩ avoids a consistency lemma for the whole semantics.) `select-correct` needs every global definition to have at least 2 locals, because the denotational CFG semantics reads slots with bound `locals` while the X86 prologue writes slots 0 and 1; compiled programs satisfy it, so the `compile-x86` theorems have no extra precondition. The main costs are `case`, which needs the invariant that no slot holds both an `inl` and an `inr` (from the consistent binders), and about 85 lines of monotonicity of CFG tails in the store for the prologue's strict moves (`Mono`, `frame-≃`).

## Adequacy for X86

Soundness and adequacy of the X86 semantics for the X86 machine (`Adequacy/X86.agda`), and with them the end-to-end theorem for `compile-x86` (`EndToEnd.agda`): for a closed ISWIM term M, the ISWIM machine terminates with a constant c exactly when the X86 machine running `compile-x86 M` does, and one terminates with an answer exactly when the other does. As for Clos5, the proof goes through the denotations: ISWIM adequacy, the denotational `compile-x86-correct-const` and `-nonempty`, and X86 adequacy.

| module | lines |
|---|---:|
| `X86Common` (runs, frames, blocks, where a definition sits in the table) | 89 |
| `X86Soundness` | 792 |
| `X86LogRel` | 328 |
| `X86` (the theorems) | 34 |
| `X86WF` (well-formed programs) | 34 |
| `X86CompileWF` (compiled programs are well formed) | 234 |
| end to end, the `compile-x86` theorems | 15 |

What it needed:

* **The machine to agree with the semantics at calls.** The X86 semantics gives the code of a definition as Λ X. Λ Y. (the body, with X in `%rdi`, Y in `%rsi`, `%rax` unset and no flag); a call applies it to finite parts of `%rdi` and `%rsi`, and continues with the result in `%rax`, all strictly. The machine passed the caller's `%rax` and flag to the callee and ran calls and returns with unset registers, so soundness was false for programs that read them (for example, a callee whose body is just `retq`); the machine, the interpreter and the informal semantics were changed to match (see above).
* **Soundness by finite approximations.** As for Clos5, a state denotes a set (`𝒮`) that every step only shrinks; the call stack is the continuation of the continuation-passing semantics. But the semantics binds a slot to a finite part of the value written, and a call to finite parts of `%rdi` and `%rsi`, and the X86 semantics has no continuity lemma. So a state denotes the meaning of its code for some finite, consistent approximation of each location (`Ap`); a step that writes v is matched by approximating the operands it reads by enough to compute the part of v the destination holds afterwards (`grow`, `write`, with the parts of pairs, tuples and injections picked out of the approximation), and by the monotonicity of the semantics (`Mono`, with the trivial conditions it needs inside a body, 115 lines). A call builds, from the callee's approximation, the entries X ↦ (Y ↦ w) of its code that the caller applies.
* **A logical relation as for Clos5** (`Values.Rel`, shared): code is related by runs of the machine, on any stack, to a return of a related value (`Ret`); the fundamental lemma is by induction on the instructions of a block, given that the blocks it may jump to are adequate. A call returns the same value for every element of its denotation, by determinism.
* **Well-formedness** (`X86WF`), which `compile-x86` produces (`X86CompileWF`): each label refers to an older definition (the semantics gives each definition the table of the older ones; soundness), each slot read is within the frame (a slot beyond it reads as `init`; adequacy), and the table is consistent (approximations must be consistent to be bound; soundness). The first two go through every pass after globalize: remove complex operands keeps scoping and references (`ws-rco`, `rb-rco`, 98 lines), lift locals gives the variables in scope at depth d slots below d in a frame of at least d slots, and explicate control and select instructions keep the atoms. Consistency is not proved for the X86 semantics; for compiled programs it comes from the table lemmas of the denotational proofs (select, explicate control, lift locals, rco) and the consistency of the Clos5 table, in a few lines.

## Language-independent infrastructure

Code that other languages and compilers would use unchanged is reported in its own table and is not in any total. It is what a textbook or a verified compiler sets up once, before any particular language: Schmidt's semantic algebras and Winskel's metalanguage of domain constructions play this role for denotational semantics, and CompCert's general-purpose libraries and its generic transition systems and simulation diagrams (`Smallstep.v`) for the CompCert style. The test is applied evenly to the three styles: would another language or compiler reuse the module as it is?

* **Infrastructure:** the abt library and the lemmas about the syntax of any signature (`Syntax/`: renaming, scoping, uses), list lookups (`ListUtil`), base types and `_⇔_` (`Primitives`, `Iff`); the denotational framework (sets as predicates, environments, the semantics of any signature and its monotonicity and consistency, `RenameSem`); the graph model, `GraphModel/` (formerly `Compiler/Model/Graph/Domain/ISWIM/`: values and consistency, the operators with their monotonicity, consistency and continuity, continuity of a semantics in its environment, formerly `Sem/Continuous`); the small-step framework (`Smallstep`, `Simulation`) and the clocked one (`Clocked`), both now parameterized over the type of observations (and, for `Clocked`, the observation of going wrong).
* **Not infrastructure:** the meaning of this compiler's primitives (`Model/Graph/Prim.agda`: `out`, `primD` and its lemmas), which stays in the denotational semantics row, as `prim?` stays in each machine and interpreter; this compiler's observations (`Observation.agda`) and the instances of the two operational frameworks at them (`Operational/Smallstep.agda`, `Operational/Simulation.agda`, `Functional/Clock.agda`). The operational values are not infrastructure either: each language's `Val` is its own small datatype, closures over that language's terms or code pointers into its tables, observed through this compiler's observations, so no other language would reuse it as it is.
* **What it changed in the totals:** the rows "generic infrastructure" and "domain, operators, continuity" are gone, and so are the shared modules that became infrastructure; see [History](#history).

The script checks that no infrastructure module imports a module that is not infrastructure.

| language-independent infrastructure | lines | used by denotational | used by CompCert-style | used by CakeML-style |
|---|---:|---:|---:|---:|
| abstract binding trees | 220 | 220 | 220 | 220 |
| syntax lemmas (renaming, scoping, uses), list lookups | 273 | 212 | 273 | 273 |
| base types, logical equivalence | 26 | 22 | 26 | 26 |
| denotational framework | 395 | 395 | — | — |
| graph model: values, operators, continuity | 512 | 512 | — | — |
| small-step framework: transition systems, simulations | 187 | — | 187 | — |
| clocked big-step framework | 80 | — | — | 80 |
| **total** | **1693** | **1361** | **706** | **599** |

The denotational proof relies on twice as much infrastructure as the CompCert-style one: the graph model and the denotational framework (907 lines) against the small-step framework (187). Adequacy uses 1519 lines of it, 158 of them (`Smallstep`, `Iff`, `Syntax.Scope`, `Syntax.ScopeRename`) not used by the denotational proof.

## The CakeML-style proof

Each interpreter is `eval : ℕ → Env → AST → Result Val`, where `Result Val` is `timeout`, `wrong` or `ret v`. It is defined by recursion on the clock and the term. The clock goes down only at a function call, and a call with clock 0 times out. The interpreter goes wrong exactly where its machine gets stuck, and it evaluates in the same order: left to right, with the operator checked to be a function before the argument is evaluated (in Clos4 and Clos5: at the call, after all three operands).

No pass adds or removes function calls. Enclose, optimize, concretize and globalize map each application to one application. Delay maps it to a `let` around one application, and `let` does not tick. So every pass is proved **clock for clock**: for every clock, the program and its compilation both time out, both go wrong, or both return related values. A generic lemma (`clocked`, 17 lines) turns this into both directions of the end theorem. There is no determinism argument and no simulation diagram. The end theorem `compile-correct` in `CompilerFuel` composes the five results with `equiv-trans`, for the same `compile` and the same precondition (a closed ISWIM program) as `CompilerSim`.

The value relations and environment agreements are the same as in the CompCert-style proofs. The saving is in everything the machines add: the continuation relation, one case per frame, and the states where one machine is ahead of the other. Pass by pass (CakeML-style against CompCert-style):

* **enclose (162 against 222).** The difference is the continuation relation and the per-frame cases: a step of a frame becomes a `>>=` and `bind-rel`. Building a closure takes several Clos2 steps for one ISWIM step, which the machine proof matches by a plus; the interpreter just evaluates the captured variables.
* **optimize (194 against 273).** The source evaluates the free variables that the optimized closure drops, and the target does not. The machine proof needs a measure simulation: a match indexed by a natural number that each such stuttering step decreases, with states for the middle of dropping a variable. The interpreter has **no stuttering index**: a dropped free variable is a variable, which makes no call and, in a well-scoped program, cannot go wrong, so the two interpreters call functions in lock step.
* **concretize (152 against 218).** A free variable becomes a projection from the tuple, three Clos3 steps for one Clos2 step, and building a closure takes one extra step. The machine proof relates a Clos2 state to a Clos3 state that is ahead of it (`Reach`, `enter`). The interpreter proof has **no run-ahead states**: a projection ``get i ⦅ ` 1 ⦆`` and the tuple of free variables are each evaluated in one go, with no intermediate state to relate.
* **delay (116 against 168).** An application becomes `let x = L' in app (fst x) (snd x) (shift M')`. The machine proof needs the run-ahead state `retT` and the four administrative steps that reach it. The interpreter proof has **no run-ahead state**: the `let`, `fst` and `snd` compute away, and `let` does not tick.
* **globalize (134 against 189).** Both proofs use the same **table-indexed relation**: the Clos5 program runs with the table D that the pass made for the whole program, the relation is indexed by D, and code `fun N` is related to `code k` when the table made by globalizing N is part of D. The lemmas about growing tables are shared. The difference is again the continuation relation and the frames.
* **composition (37 against 32).** Agda cannot infer the intermediate programs through the interpreters' `sem`, so the CakeML-style composition names them.

As of PR #26 (rco), the clocked interpreters (364 lines) are smaller than the machines (471): no continuations and no states. The generic part (80 lines against 188, now infrastructure: `Clocked` 80, `Smallstep` and `Simulation` 187) has no transition systems, simulations or determinism lemmas. In all, the CakeML-style proof was 1980 lines against 2653, both counting the 443 lines of shared syntactic lemmas and observations that only the two operational proofs use (165 before rco).

## Why delay costs more on the denotational side

As of PR #24, before arithmetic; the denotational proof of delay was 824 lines and the CompCert-style one 151 (now 859 and 168, see [History](#history)).

**Denotational** (`Correctness/Delay*.agda`):

| part | lines | what it is |
|---|---:|---|
| **backward direction (reflect)** | **479** | |
| – finite-observation machinery | 195 | the relation R with the call batches (130), depth and `Bnd` (26), `collect` (39), which extracts finite witnesses of a target call |
| – fundamental lemma | 193 | one case per construct, plus helpers for nonemptiness, tags, pairs and case branches |
| – semantic side conditions | 48 | consistency of Clos4 terms (16); a source β-law and a "one finite part of the bound variable suffices" lemma (32) |
| – imports and end theorem | 43 | |
| **forward direction (preserve)** | **208** | |
| – the relation ⊑ and its lemmas | 44 | |
| – target laws | 41 | a β-law for closures, `case` contains its branch, one finite part suffices |
| – fundamental lemma | 78 | |
| – imports and end theorem | 45 | |
| **shared** | **137** | |
| – the `let`/`fst`/`snd` application equation | 42 | `DelayApp` |
| – shorthands, list helpers, flat values, `cdr-witness` (finitely many pairs whose cdrs cover a list) | 95 | |

**CompCert-style** (`Correctness/DelaySim.agda`):

| part | lines |
|---|---:|
| relations: values, terms, environments, continuations; the run-ahead state | 58 |
| the simulation, all cases | 66 |
| end theorem | 7 |
| imports | 20 |

Its renaming lemmas, generic over any syntax (43 lines), are now language-independent infrastructure (`Syntax/Rename.agda`) and not counted.

**Where the ≈ 5.5× comes from:**

1. **Two directions instead of one: about 479 lines.** Delay changes how functions are represented, so the result is not an equation, and preserve and reflect need different relations. In the CompCert-style proof, the backward direction comes from forward simulation plus determinism. The generic framework proves that once, and it is counted there. Preserve alone plus the shared part is about 345 lines, roughly 2.3× `DelaySim`.
2. **Finite observations in reflect: about 195 lines, plus part of the app case.** Pairs are joined (one value ⦅ u , v ⦆), but a target call still takes its code from `car C` and its free variables from `cdr C` separately, possibly from different pairs. A single target value says nothing about a call, so the relation ranges over finite lists, with batches and a depth index.
3. **β needs side conditions: about 130 lines.** In the graph model, β for closures, `let` and `case` holds only with nonemptiness and continuity. That costs `clos-β` and `cont-0` on both sides, the application equation, and consistency for `case`. Operationally, β is a machine step.
4. **Imports: 82 lines against 20.**
5. **Per-construct cases are comparable once the plumbing is gone.** Preserve's fundamental lemma is 78 lines against 66 for the simulation cases.

The cost is not in the compositional, per-construct reasoning. It is in the backward direction forced by the change of representation (item 1), and in the side conditions β needs in the graph model (item 3). The CompCert-style proof pays for the backward direction once, through determinism. The denotational proof pays for it in each pass that is not an equation, and delay is the only such pass.

## Experiment: a direct backward simulation for delay

The numbers in this section are as of PR #24, before arithmetic, which added 3 lines to `DelayBackSim` (149) and 17 to `DelaySim` (168); see [History](#history).

The CompCert-style proof gets the backward direction of every pass from forward simulation plus determinism. A non-deterministic language cannot do that. This experiment measures what it would pay instead: the backward direction of delay, proved by a backward simulation that uses the determinism of neither machine. It is the CompCert-style counterpart of the denotational reflect.

* `Operational/Backward.agda` (framework). A CompCert-style backward simulation. The target moves, and the source answers each target step with a plus, or with a star that decreases a well-founded measure. A target stop with o is answered by a source star to a stop with o. Since the machines are total, no source-safety premise is needed. The end theorems are:
  * `backward-terminates : Terminates L₂ o → Terminates L₁ o`, for every o including o-wrong;
  * `backward-diverges : Diverges∞ L₂ → Diverges∞ L₁`, where `Diverges∞` is an infinite run. Without determinism, "runs of every length" (`Diverges`) does not give an infinite run, so the hypothesis must be one. The measure makes the simulation productive: along an infinite target run, the source cannot wait forever.
* `Correctness/DelayBackSim.agda` (delay). The end theorems are `delay-back-terminates` and `delay-back-diverges`, for every Clos3 program. It reuses DelaySim's relations on values, environments and continuations (58 lines), and the shared renaming lemmas. The new part is the state relation. Where the target takes administrative steps for one source step, the source waits and the index counts the target steps left:
  * 3 when building a closure;
  * 9 when a call returns its operator to the let frame: the let body, fst, the variable, the pair check, then snd, the variable, and the return to appE.

  These intermediate target states are listed one by one. The forward proof jumps over them with a target star, and it needs only one run-ahead state (`retT`).

| | lines |
|---|---:|
| delay, forward (`DelaySim`) | 151 |
| delay, direct backward (`DelayBackSim`) | 146 |
| – the same, standalone (with the 58 reused lines) | ≈ 204 |
| generic: backward from forward + determinism (in `Smallstep`, `Simulation`) | 71 |
| generic: direct backward simulation (`Backward`) | 94 |
| delay, denotational reflect (`DelayReflectFinite` + `DelayFiniteRel`) | 453 |

The 71 lines are the parts of the forward framework that exist only to get the backward direction: the determinism lemmas `step-det`, `final-det` and `final-nostep`, `star→steps`, `steps-det-skip`, `diverges-not-terminates`, `never-final-diverges`, `back` and its measure, `backward-terminates`, and `equivalent`. They are paid once for all five passes.

**What this shows:**

* A direct CompCert-style backward proof of delay is about as big as the forward one: 146 lines on top of the shared relations, or about 204 standalone, against 151. The cases are as easy as the forward cases (one line each, by computation of the step function). The extra lines list the administrative target states, 12 constructors of the state relation and one `waits` line per state.
* It stays well under the denotational reflect (453 lines in its two modules, 479 with the depth bound it uses). So the CompCert-style advantage on delay is not only "backward comes free from determinism". Even without determinism, a step-indexed backward simulation needs no finite-observation machinery. A target run is a finite sequence of steps, each answered locally, while a denotational element of a target application summarizes many calls at once.
* Generically, the direct backward framework (94) is somewhat larger than the determinism argument (71). And a non-deterministic language would need it alongside a forward simulation in every pass that changes representation, here about 150 lines more for delay. The determinism argument is paid once.
