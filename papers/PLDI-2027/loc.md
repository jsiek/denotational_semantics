# Size of the three compiler-correctness proofs

All three proofs establish end-to-end correctness for the same compiler, `compile`, which runs
ISWIM --enclose--> Clos2 --optimize--> Clos2 --concretize--> Clos3 --delay--> Clos4 --globalize--> Clos5.
Each also proves two more passes, after Essentials of Compilation, and the compilers that extend `compile` with them, end to end: remove complex operands (rco, Clos5 --rco--> Clos5, into monadic normal form; `compile-mon`, see [Remove complex operands](#remove-complex-operands)) and lift locals (monadic Clos5 --lift--> Imp, an imperative language with frames of mutable slots; `compile-imp`, see [Lift locals](#lift-locals)).

* **Denotational:** a graph-model semantics for each language and one correctness proof per pass, in `agda/Compiler/Model/Graph/`. The theorem is `CompilerCorrect`: the source and compiled program produce the same constants, and one denotation is nonempty exactly when the other is.
* **CompCert-style:** a small-step CEK machine for each language and one forward simulation per pass, in `agda/Compiler/Operational/`. The theorem is `CompilerSim`: the two programs terminate with the same observation, including going wrong, and one diverges exactly when the other does.
* **CakeML-style:** a functional big-step semantics with a clock for each language (a total interpreter that ticks the clock at each function call and times out when it runs out) and one clock-for-clock proof per pass, in `agda/Compiler/Functional/`. The theorem is `CompilerFuel`. It has the same shape as the CompCert-style one, over the same observations: a program terminates with o if it does so for some clock, and diverges if it times out for every clock.

Counts are code lines: lines that are neither blank nor comments. The tables are regenerated with
`python3 papers/PLDI-2027/loc.py` from the repository root. The script fails if any Agda module is not assigned to a group, or if one proof imports another proof's modules or adequacy's.

**How totals are computed.** Each module belongs to one group: one of the three proofs, adequacy, shared, examples, or the experiment. A proof's total is its own modules plus every shared module that it imports, directly or transitively, *unless all three proofs import it*. So each column is the standalone size of that proof, apart from what is common to all three: the abt library, the languages, the compiler passes and `compile` (`Compiler/Compile/Pipeline.agda`), and the lemmas all three use. Those are not counted in any column. A shared module that only some proofs use is counted in each of them; it is the row "shared modules not used by all three proofs", listed [below](#shared-modules). Examples are not counted. Adequacy is reported separately (see below). The import graph is read from the `import` and `open import` lines.

## Current counts

As of this PR:

| component | denotational | CompCert-style | CakeML-style |
|---|---:|---:|---:|
| generic infrastructure | 303 | 188 | 80 |
| domain, operators, continuity | 482 | — | — |
| semantics of the languages | 665 | 567 | 425 |
| enclose | 101 | 222 | 162 |
| optimize | 155 | 273 | 194 |
| concretize | 242 | 218 | 152 |
| delay | 859 | 168 | 116 |
| globalize | 242 | 189 | 134 |
| rco | 237 | 449 | 298 |
| lift locals | 204 | 218 | 143 |
| composition | 49 | 32 | 37 |
| shared modules not used by all three proofs | 28 | 443 | 443 |
| **total** | **3567** | **2967** | **2184** |

Adequacy relates the denotational semantics of ISWIM and Clos5 to their machines. It turns `CompilerCorrect` into a statement about running programs (`Adequacy/EndToEnd.agda`). It is reported separately, because the denotational semantics can be taken as *the* semantics of a language, in which case adequacy is not needed. It is an add-on to the denotational proof, so its total also counts the shared modules it imports that the denotational total does not already count (the observations, closedness, well-scopedness, the scoping of `compile`'s output and growing tables, 443 lines); the denotational total plus the adequacy total is then standalone, except for the machines (471 lines), which adequacy reuses from the CompCert-style proof and which are not counted again.

| adequacy (denotational side only) | lines |
|---|---:|
| ISWIM | 798 |
| Clos5 | 847 |
| well-formedness of compiled programs | 60 |
| end to end | 24 |
| shared modules not used by all three proofs, nor by the denotational one | 443 |
| **total** | **2172** |

An experiment, not in the totals, is described [below](#experiment-a-direct-backward-simulation-for-delay):

| experiment (not in the totals) | lines |
|---|---:|
| CompCert-style: direct backward simulation for delay — framework | 94 |
| CompCert-style: direct backward simulation for delay — delay | 149 |

### Shared modules

| shared module | lines | used by |
|---|---:|---|
| `Compiler.Compile.Concretize` | 57 | all three proofs |
| `Compiler.Compile.Delay` | 32 | all three proofs |
| `Compiler.Compile.Enclose` | 33 | all three proofs |
| `Compiler.Compile.EncloseScope` | 55 | CompCert-style, CakeML-style, adequacy |
| `Compiler.Compile.Globalize` | 52 | all three proofs |
| `Compiler.Compile.GlobalizeTable` | 52 | CompCert-style, CakeML-style, adequacy |
| `Compiler.Compile.LiftLocals` | 44 | all three proofs |
| `Compiler.Compile.Optimize` | 62 | all three proofs |
| `Compiler.Compile.Pipeline` | 20 | all three proofs |
| `Compiler.Compile.PipelineScope` | 249 | CompCert-style, CakeML-style, adequacy |
| `Compiler.Compile.RCO` | 120 | all three proofs |
| `Compiler.Lang.Clos2` | 39 | all three proofs |
| `Compiler.Lang.Clos3` | 39 | all three proofs |
| `Compiler.Lang.Clos4` | 53 | all three proofs |
| `Compiler.Lang.Clos5` | 62 | all three proofs |
| `Compiler.Lang.ISWIM` | 39 | all three proofs |
| `Compiler.Lang.Imp` | 35 | all three proofs |
| `Compiler.Lang.ListUtil` | 62 | all three proofs |
| `Compiler.Lang.Mon` | 52 | all three proofs |
| `Compiler.Lang.Prim` | 13 | all three proofs |
| `Compiler.Lang.Rename` | 65 | all three proofs |
| `Compiler.Lang.Scope` | 32 | CompCert-style, CakeML-style, adequacy |
| `Compiler.Lang.ScopeRename` | 29 | CompCert-style, CakeML-style, adequacy |
| `Compiler.Lang.Uses` | 55 | all three proofs |
| `Compiler.Observation` | 26 | CompCert-style, CakeML-style, adequacy |
| `NewSigUtil` | 6 | all three proofs |
| `NewSyntaxUtil` | 9 | all three proofs |
| `Primitives` | 22 | all three proofs |
| `abt.AbstractBindingTree` | 18 | all three proofs |
| `abt.Fold2` | 28 | denotational, adequacy |
| `abt.GSubst` | 9 | all three proofs |
| `abt.ScopedTuple` | 137 | all three proofs |
| `abt.Sig` | 18 | all three proofs |
| `abt.Var` | 23 | all three proofs |

Shared by all three proofs, and not counted: 27 modules, 1176 lines. Counted in the denotational total: `abt.Fold2` (28), the fold of the abt library, used by its generic semantics. Counted in both operational totals and in adequacy: `Compile.EncloseScope` (55), `Compile.GlobalizeTable` (52), `Compile.PipelineScope` (249), `Lang.Scope` (32), `Lang.ScopeRename` (29) and `Observation` (26), 443 lines. Examples, not counted: 230 lines.

## What the groups contain

* **shared (counted only in the proofs that use it when not all three do, see above):** the abt library, the languages, the compiler passes and their composition `compile` (`Compile/Pipeline.agda`), which all three proofs use; the observations and the end-theorem shape (`Compiler/Observation.agda`); and the machine-independent lemmas that both operational styles use:
  * `Lang/ListUtil.agda`: lookup in an environment, projection from a tuple, and lemmas about lookups (formerly `Operational/Machine/Common.agda`, plus list lemmas from `ConcretizeSim` and `GlobalizeSim`);
  * `Lang/Scope.agda`: well-scoped terms for any signature and `ws-uses` (from `OptimizeSim`);
  * `Lang/ScopeRename.agda`: renaming preserves well-scopedness (formerly adequacy's `Scope`);
  * `Lang/Rename.agda`: the renaming lemmas `rename-cong`, `rename-fuse`, `rename-id` (from `DelaySim`);
  * `Compile/EncloseScope.agda`: closed ISWIM programs and `enclose-closed` (from `EncloseSim` and `OptimizeSim`);
  * `Compile/GlobalizeTable.agda`: growing tables `_⊑_`, `glob-grows` and `global-⊑` (from `GlobalizeSim`); the table lookup `global` itself moved to `Lang/Clos5.agda`, so the machine and the interpreter use the same one;
  * `Compile/PipelineScope.agda`: well-scoped Clos5 programs (`Scoped`, the precondition of both operational rco proofs) and `compile-scoped`, that `compile` produces them from closed ISWIM programs, one lemma per pass (formerly the well-scopedness half of adequacy's `CompileWF`). Only the end-to-end `compile-mon` theorems of the operational proofs use it.
* **generic infrastructure:**
  * denotational: sets as predicates, environments, generic semantics, monotonicity and continuity over operator signatures;
  * CompCert-style: small-step transition systems, forward simulation, and the iff end theorem;
  * CakeML-style: results with timeout, the clocked end theorem, and the lemma that related results for every clock give it. It imports nothing from the CompCert-style development.
* **domain, operators, continuity:** the graph-model values, consistency, the semantic operators and their monotonicity, consistency and continuity lemmas.
* **semantics of the languages:**
  * denotational: the semantics of ISWIM, Clos2 through Clos5 and Imp, plus the continuity instances the proofs use (for Clos5, `Sem/Clos5IswimContinuous.agda`, used by rco and by adequacy);
  * CompCert-style: the six machines (ISWIM, Clos2–Clos5 and Imp);
  * CakeML-style: the six clocked interpreters (Clos5's and Imp's take the table of global definitions).
* **one row per pass:** that pass's correctness proof. The rco row also contains the end-to-end theorem for `compile-mon`, a corollary of the composition and the rco theorem (11 lines in the denotational proof, 2 in each operational one), in all three styles; likewise the lift-locals row contains the end-to-end theorem for `compile-imp`.
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

  The cost falls only on passes that change representation. When ⟦pass M⟧ ≃ ⟦M⟧ (enclose, optimize, concretize, globalize), both directions come from the equation at once, with no determinism argument.
* **Machines.** The ISWIM, Clos2 and Clos3 machines check that an operator is a function before evaluating the argument. Delay needs this to preserve going wrong: it takes the closure apart with `fst` before the argument. The Clos4 and Clos5 machines check that the operator is code only at the call, after all three operands, like an indirect call instruction, so that rco, which let-binds all the operands before the call, preserves going wrong. On delay's output the late check always passes, since a non-closure has already gone wrong at `fst`.

* **Clos5 continuity is denotational.** The continuity of the Clos5 semantics in the environment (117 lines), formerly adequacy's `Clos5Continuous`, is now `Model/Graph/Sem/Clos5IswimContinuous.agda`, in the denotational row "semantics of the languages", because the rco proof uses it (for the let laws). Adequacy reuses it from there and does not count it again; adequacy's Clos5 row shrank by the same 117 lines.
* **The rco preconditions differ.** The denotational rco theorem is an equation with no precondition on programs; both operational ones need `Scoped`, and their end-to-end `compile-mon` theorems therefore pay for `compile-scoped` (278 lines with `ScopeRename`, in the shared row). See [Remove complex operands](#remove-complex-operands).
* **Lift locals needs no precondition in any style.** A variable out of scope becomes a slot beyond the frame, which goes wrong (operationally) or reads as `init` (denotationally) exactly where the Clos5 variable does. See [Lift locals](#lift-locals).
* **Adequacy stops at Clos5.** The end-to-end denotational theorems for `compile-mon` and `compile-imp` speak about the denotations of Clos5 and Imp; adequacy (and so a statement about running code) exists only for ISWIM and Clos5. Adequacy for the final target language is still to do.

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
| 2026-10-12 | lift locals into Imp, all three proofs (this PR) | 3567 (+278) | 2967 (+314) | 2184 (+204) |

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

## Remove complex operands

The pass (`Compile/RCO.agda`, Clos5 → Clos5, shared) binds every complex operand of a construct to a fresh variable by a `let`, left to right, and leaves atoms (variables, literals, code pointers) in place, shifted under the new lets; the result is in monadic normal form (`Lang/Mon.agda`). It adds no calls and `let` does not tick. The late code check in the Clos4 and Clos5 machines and interpreters (see [Caveats](#caveats)) was added for this pass: with the check right after the operator, `app ⦅ L , M , N ⦆` with a non-code L goes wrong before M runs, while its rco, `let x = L in let y = M in …`, would run M first.

* **Denotational (237 lines): an exact equation.** `rco-correct : ⟦ rco M ⟧[ T ] ρ ≃ ⟦ M ⟧[ T ] ρ` for nonempty ρ, and `rco-program-correct : ⟦ rco-program P ⟧ₚ ≃ ⟦ P ⟧ₚ` for **every** program, with no scoping precondition. The laws are that `let` is strict and otherwise substitutes the meaning of its right-hand side (`let-strict`, `let-β`, which uses the continuity of Clos5), and that every construct whose operands rco names is a strict congruence (`Strict`); one lemma for the let chain (`lift-≃`) then gives each construct in one line. Order of evaluation is invisible: going wrong and divergence both denote ∅, and an unbound variable denotes {ω}.
* **CompCert-style (449 lines).** A forward simulation of the Clos5 machine by itself, for programs in `Scoped`. The target environment has the values of the lets in front, so terms are related up to a renaming (`Ren`). The source frames of a construct are related to the target's remaining let chain by `Pend` (one constructor per operand: a complex operand runs in lock step under a let frame, an atom is evaluated by the source while the target waits, with a decreasing index, and at the end the target runs the construct on its atoms up to the same final frame, `retT`).
* **CakeML-style (298 lines): clock for clock, with equality of results.** For `Scoped` programs, `eval ds ck ρ M ≡ eval (map rco ds) ck ρ (rco M)` for every clock (`run≈`): values contain no code, so they are equal, not just related. The key lemma is the let chain (`lets≈`): evaluating the chain evaluates the complex operands left to right and then the construct with the atoms bound to their values; renaming commutes with evaluation (`ren`).

**Why the operational proofs need `Scoped`.** An atom left in place is evaluated after the complex operands that follow it. An unbound variable goes wrong when it is evaluated, so it would go wrong later: ``pair (` 0) L`` with L a loop goes wrong in the empty environment, while its rco, ``let x = L in pair (` 1) (` 0)``, diverges. In the denotational semantics both denote ∅, so the equation holds anyway. `Scoped` (main closed, each definition in its two parameters) rules this out; the compiler produces such programs (`compile-scoped`, 249 + 29 lines, counted in both operational totals because only their `compile-mon` theorems use it).

## Lift locals

The pass (`Compile/LiftLocals.agda`, shared, 44 lines) takes a monadic Clos5 term to Imp (`Lang/Imp.agda`, shared, 35 lines). Imp has no binders: each body declares a frame of slots, a variable names a slot, `let` becomes the assignment `x := e₁; e₂`, and `case` assigns the payload to a slot. The frame is threaded: an assignment is seen by everything that runs after it in the same frame, also after the expression that contains it. A call runs the callee in a fresh frame (free variables in slot 0, argument in slot 1) and leaves the caller's frame as it was; reading or assigning a slot beyond the frame goes wrong. Slots are de Bruijn levels: the variable x at depth d is slot d ∸ (x + 1), and a `let` or `case` at depth d assigns slot d, so code at depth d assigns only slots that no variable in scope names. The frame has d₀ + height slots (height = deepest nesting of binders), and a variable out of scope becomes slot n, beyond the frame. No proof needs a precondition, and the semantics of Imp in each style is new:

| component | denotational | CompCert-style | CakeML-style |
|---|---:|---:|---:|
| semantics of Imp | +74 | +96 | +61 |
| lift locals | +204 | +218 | +143 |
| **total** | **+278** | **+314** | **+204** |

* **Denotational (74 + 204).** A store σ : ℕ → 𝒫 Value gives each slot a set of values, and an expression means, for the store it enters with, a set of values and the store it leaves (`Sem/Imp.agda`). `x := e₁; e₂` is Clos5's strict let, `⋆ ⟨ Λ F , D₁ ⟩`, applied both to the value and to each slot of the store e₂ leaves (`letₛ`); `case` is `𝒞`, likewise pointwise (`caseₛ`). Reading or assigning beyond the frame gives `init`, as an out-of-scope variable does in Clos5. The proof (`lift-sem`) shows at once that the value of `lift n d M` is ≃ `⟦ M ⟧ ρ` and that the slots below d of the store it leaves are those it entered with (`Pres`), given that the store agrees with ρ (`Agree`) and `d + height M ≤ n`. Each simple construct is one congruence line; let and case reuse rco's `strict-≃`, `⋆-≃`, `Λ-≃` and `𝒞-≃`. `Pres` holds only when the value is nonempty, since a stuck case or a let whose right-hand side has no value empties every slot too. No continuity is needed.
* **CompCert-style (96 + 218).** The Imp machine (`Machine/Imp.agda`) carries the frame in its states and evaluates each atom in its own step, through the same continuation frames as the Clos5 machine, plus `assignK`, `caseK` and `callK` (which restores the caller's frame). A frame is related to the environment as `Fr n ρ (ρ ʳ++ τ)`: the environment reversed, then the free slots, n in all, so going under a binder is definitional. Continuations are related by `Kont` (one case per Clos5 frame, plus `weak`, a continuation at depth d is one at depth d + 1, which is where "code at depth d assigns only slots ≥ d" lives, and `call` for `callK`). Every source step is matched by exactly one target step, followed by any `callK` pops (`plus-simulation`, no measure); about half of the 70 lines of `sim` are one-line wrong-value cases.
* **CakeML-style (61 + 143).** The interpreter `eval : ℕ → Frame → Exp → Result (Val × Frame)` ticks only at calls, like Clos5's, so the proof is clock for clock (`sim`), with values related by `≡` (Imp reuses Clos5's values) and frames by the same `Fr n ρ` as the CompCert-style proof.

Unlike rco, the denotational proof is not the smallest here: the store is the new ingredient, and in the graph model it is a second, pointwise output (`Pres` and the store halves of `letₛ`/`caseₛ`), while the operational proofs get the frame-preservation fact structurally (`ʳ++`, `weak`).

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

The clocked interpreters (364 lines) are smaller than the machines (471): no continuations and no states. The generic part (80 lines against 188) has no transition systems, simulations or determinism lemmas. In all, the CakeML-style proof is 1980 lines against 2653, both counting the 443 lines of shared syntactic lemmas and observations that only the two operational proofs use (165 before rco).

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

Its renaming lemmas, generic over any syntax (43 lines), are now shared (`Lang/Rename.agda`) and, since all three proofs use them, not counted.

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
