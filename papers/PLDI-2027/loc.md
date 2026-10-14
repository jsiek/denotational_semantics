# Size of the four compiler-correctness proofs

All four proofs establish end-to-end correctness for the same compiler, `compile`, which runs
ISWIM --simplify--> ISWIM --enclose--> Clos2 --optimize--> Clos2 --concretize--> Clos3 --delay--> Clos4 --globalize--> Clos5
(simplify, a source optimizer, since PR #40, with inlining since PR #41; see [Simplify](#simplify)).
Each also proves four more passes, after Essentials of Compilation, and the compilers that extend `compile` with them, end to end: remove complex operands (rco, Clos5 --rco--> Clos5, into monadic normal form; `compile-mon`, see [Remove complex operands](#remove-complex-operands)), lift locals (monadic Clos5 --lift--> Imp, an imperative language with frames of mutable slots; `compile-imp`, see [Lift locals](#lift-locals)) and explicate control (Imp --explicate--> CFG, a C-like language of blocks; `compile-cfg`, see [Explicate control](#explicate-control)) and select instructions (CFG --select--> X86, x86 with variables over abstract values; `compile-x86` = select ∘ `compile-cfg`, see [Select instructions](#select-instructions)).

* **Denotational: graph model** ("graph model" in short): a graph-model semantics for each language and one correctness proof per pass, in `agda/Semantics/Graph/` (the proofs under `agda/proof/Correctness/Graph/`, the lemmas about the semantics under `agda/proof/Semantics/Graph/`), over the graph model in `agda/Framework/GraphModel/`. The theorem is `CompilerCorrect`: the source and compiled program produce the same constants, and one denotation is nonempty exactly when the other is.
* **CEK machine + simulation** ("simulation" in short; the style of CompCert): a small-step CEK machine for each language (for X86, a machine with a call stack, registers and a flag) and one forward simulation per pass, in `agda/Semantics/CEK/` (the proofs under `agda/proof/Correctness/CEK/`). The theorem is `CompilerSim`: the two programs terminate with the same observation, including an error, and one diverges exactly when the other does.
* **Clocked interpreter + value relations** ("interpreter" in short; the style of CakeML): a functional big-step semantics with a clock for each language (a total interpreter that ticks the clock at each function call and times out when it runs out) and one clock-for-clock proof per pass, relating the results of the two interpreters by a relation on values (equality for rco, lift locals, explicate control and select instructions), in `agda/Semantics/Interp/` (the proofs under `agda/proof/Correctness/Interp/`). The theorem is `CompilerFuel`. It has the same shape as the simulation one, over the same observations: a program terminates with o if it does so for some clock, and diverges if it times out for every clock. The interpreters are written in Agda's do-notation, which desugars to the same binds `_>>=_` of the result monad.
* **Reduction semantics + simulation** ("reduction" in short; small-step reduction by substitution, as in PLT Redex, with CompCert-style simulations): a reduction semantics by substitution for each language with binders (ISWIM, Clos2–Clos5), a step function written with congruence rules, and one forward simulation per pass between terms, in `agda/Semantics/Reduction/` (the proofs under `agda/proof/Correctness/Reduction/`), over the reduction framework `agda/Framework/Reduction.agda` and the substitution library `agda/Framework/Syntax/Subst.agda` (infrastructure). Imp, CFG and X86 have no binders, so a reduction semantics for them would be the configuration-stepping machine they already have: they keep the machines of the CEK column, and the proofs of explicate control and select instructions between those machines are shared with it (counted in both columns). The theorem is `Theorems/Reduction.agda`, of the same shape as the simulation one; see [Reduction semantics + simulation](#reduction-semantics--simulation).

Counts are code lines: lines that are neither blank, nor comments, nor part of an import statement (`import` or `open import`, with its continuation lines). Imports are left out because their number depends on how finely a development is split into modules, not on what it proves; they were counted until PR #35 (see [History](#history)). The tables are regenerated with
`python3 papers/PLDI-2027/loc.py` from the repository root. The script fails if any Agda module is not assigned to a group, if one proof imports another proof's modules, adequacy's or an experiment's, if a module of the language-independent infrastructure imports anything that is not infrastructure, if a module of the audit surface imports one of `agda/proof/` (the theorem files excepted), or if a module outside `agda/proof/` is not used by a theorem statement (see [Audit surface](#audit-surface)). A module split into definitions (`agda/X.agda`) and lemmas (`agda/proof/X.agda`) counts as one module, in one group.

**How totals are computed.** Each module belongs to one group: one of the four proofs, adequacy, shared, language-independent infrastructure, examples, or an experiment. A few groups belong to two proofs: the machines of Imp, CFG and X86 (with the values of the Clos5 machine, which they use, and the instance of the small-step framework) and the proofs of explicate control and select instructions are shared by the CEK and reduction proofs, and are counted in full in the corresponding rows of both. A proof's total is its own modules plus every shared module that it imports, directly or transitively, *unless all four proofs import it*. So each column is the standalone size of that proof, apart from two things. What is common to all four proofs: the languages, the compiler passes and `compile` (`Compiler/Pipeline.agda`). And the language-independent infrastructure, code that other languages and compilers would reuse unchanged (the abt library and syntax lemmas, the denotational framework and the graph model, the small-step, reduction and clocked frameworks, and substitution; see [Language-independent infrastructure](#language-independent-infrastructure)). Neither is counted in any column; the infrastructure has its own table, which shows what each proof relies on. A shared module that only some proofs use is counted in each of them; it is the row "shared modules not used by all four proofs", listed [below](#shared-modules). Examples are not counted. Adequacy is reported separately (see below). The import graph is read from the `import` and `open import` lines.

## Current counts

In every table that compares the proof styles, the lowest number of each row is in bold: the best result for that row. Tables of infrastructure are not marked, since relying on less of it is not in itself better.

As of PR #53 (after the infrastructure audit, PRs #42 and #44–#47, the graph model with errors, PRs #50 and #51, one infrastructure rule for both graph models, which moves the graph model's laws over its operators into its infrastructure (PR #51: its total 2744 → 2608), and the graph model with errors rebuilt on an error monad (PR #53: its total 3953 → 3528); see [History](#history) and [Graph model with errors](#graph-model-with-errors)). The last column is the graph model with errors, counted as the four are (plus the graph model's meaning of the primitives, which it extends) but not in their comparison: the shared modules not counted are still those all four use. The closure-conversion passes (enclose, optimize, concretize, delay, globalize) are labelled "CC: " in the tables, since `simplify`, rco and the later passes are not part of closure conversion:

| component | denotational: graph model | CEK machine + simulation | clocked interpreter + value relations | reduction semantics + simulation | graph model with errors |
|---|---:|---:|---:|---:|---:|
| semantics of the languages | **443** | 660 | 466 | 644 | 447 |
| simplify | **343** | 572 | 644 | 710 | 349 |
| CC: enclose | **81** | 188 | 140 | 186 | 90 |
| CC: optimize | **134** | 224 | 170 | 222 | 149 |
| CC: concretize | 141 | 182 | **127** | 157 | 134 |
| CC: delay | 594 | 134 | **90** | 183 | 898 |
| CC: globalize | 155 | 157 | **111** | 192 | 157 |
| rco | **118** | 396 | 245 | 247 | 194 |
| lift locals | 142 | 172 | **98** | 306 | 138 |
| explicate control | 154 | 124 | **118** | 124 | 144 |
| select instructions | 271 | 235 | **107** | 235 | 363 |
| composition | 32 | 26 | **22** | 27 | 33 |
| shared modules not used by all four proofs | — | 456 | 456 | 456 | **398** |
| the graph model's meaning of the primitives | — | — | — | — | 34 |
| **total** | **2608** | 3526 | 2794 | 3689 | 3528 |

The denotational semantics row includes the monotonicity, consistency and continuity of each language; since PR #47 they are assembled from a table of each language's operators, whose properties are proved once in the infrastructure (`Good` in `proof/Framework/GraphModel/Ops`), so the continuity of ISWIM that simplify's proof uses for β is a one-line re-export (`proof/Semantics/Graph/ISWIMContinuous.agda`). The simplify row of each column includes the syntactic lemmas about the pass that all four proofs use (`proof/Compiler/SimplifyFacts.agda`, 110 lines); that simplify keeps programs closed (`proof/Compiler/SimplifyScope.agda`, 125 lines), which only the operational compositions need, is in the shared row. The denotational lift-locals and explicate-control rows are the proofs against the continuation-passing semantics of Imp; the proofs against the direct semantics are an experiment (see [Explicate control](#explicate-control)). The reduction column's semantics row is its reduction semantics of ISWIM and Clos2–Clos5 with their values (378 lines: 274 for the reductions, 104 for their values) and the machines of Imp, CFG and X86 that it shares with the CEK column (266); its explicate-control and select-instructions rows are the CEK proofs, shared (see [Reduction semantics + simulation](#reduction-semantics--simulation)).

Language-independent infrastructure, not in any total (see [Language-independent infrastructure](#language-independent-infrastructure)); each proof column is the part of a group that the proof reaches. The graph model is three groups since PR #50: what any graph-model semantics uses (values, consistency, and the machinery for any operators: continuity, `Good`, the properties of whole terms, with constants and tuple components), the graph model's operators, and the error monad of the graph model with errors with its operators and laws (since PR #53 its operators are the graph model's under the monad, so it also reaches the graph model's operators), so that each model is charged only for the operators it uses (see [Graph model with errors](#graph-model-with-errors)); the last column is that model's (semantics and pass proofs, without its adequacy):

| language-independent infrastructure (not in the totals) | lines | used by denotational: graph model | used by CEK machine + simulation | used by clocked interpreter + value relations | used by reduction semantics + simulation | used by graph model with errors |
|---|---:|---:|---:|---:|---:|---:|
| abstract binding trees | 190 | 190 | 190 | 190 | 190 | 190 |
| syntax lemmas (renaming, scoping, uses), list lookups | 499 | 356 | 422 | 407 | 484 | 407 |
| base types, logical equivalence | 20 | 17 | 20 | 20 | 20 | 20 |
| denotational framework | 375 | 350 | — | — | — | 375 |
| graph model: values, consistency, machinery for any operators | 364 | 364 | — | — | — | 364 |
| graph model: its operators | 623 | 623 | — | — | — | 474 |
| graph model with errors: the error monad, its operators and laws | 935 | — | — | — | — | 935 |
| small-step framework: transition systems, simulations | 243 | — | 243 | — | 243 | — |
| reduction framework: reduction semantics, simulations between them | 235 | — | — | — | 235 | — |
| clocked big-step framework | 243 | — | — | 243 | — | — |
| runs of a step function from any state | 29 | — | — | — | — | — |
| typed pilot: decidable base types, collecting vectors | 48 | — | — | — | — | — |
| **total** | 3804 | 1900 | 875 | 860 | 1172 | 2765 |

Adequacy uses 2110 lines of the infrastructure, 210 of them not used by the denotational proof.

Adequacy relates the denotational semantics of ISWIM, Clos5 and X86 to their machines. It turns `CompilerCorrect`, and the end-to-end theorem for the whole compiler, `compile-x86` (`SelectCorrect`), into statements about running programs (`proof/Adequacy/EndToEnd.agda`; see [Adequacy for X86](#adequacy-for-x86)). It is reported separately, because the denotational semantics can be taken as *the* semantics of a language, in which case adequacy is not needed. It is an add-on to the denotational proof, so its total also counts the shared modules it imports that the denotational total does not already count (the observations, closedness, the scoping of `compile`'s output, that simplify keeps programs closed, and growing tables, 456 lines); the denotational total plus the adequacy total is then standalone, except for the infrastructure and for the ISWIM, Clos5, Imp and X86 machines (367 lines, plus the 1-line instance of the small-step framework; X86's frames are Imp's), which adequacy reuses from the simulation proof and which are not counted again. The last column is the adequacy of the graph model with errors (for ISWIM, Clos5 and X86, on errors, constants, answers and divergence; see [Graph model with errors](#graph-model-with-errors)), counted the same way against its own proof: the shared modules it uses that the errors column does not count (growing tables, the observations), and the graph model's adequacy modules it reuses (`Adequacy.Common`).

| adequacy (denotational side only) | graph model | graph model with errors |
|---|---:|---:|
| ISWIM | **663** | 790 |
| Clos5 | **712** | 904 |
| X86 | **1115** | 2096 |
| well-formedness of compiled programs | **262** | 364 |
| end to end | **25** | 39 |
| simplify through the ISWIM machine | — | 30 |
| shared modules not used by all four proofs, nor by the proof of its model | 456 | **58** |
| the graph model's adequacy modules it uses | — | 52 |
| **total** | **3233** | 4333 |

The typed pilot, not in the totals, has its own section, [Typed intermediate languages (pilot)](#typed-intermediate-languages-pilot). Two experiments, not in the totals: a direct backward simulation for delay, described [below](#experiment-a-direct-backward-simulation-for-delay), and the direct denotational semantics of Imp with lift locals and explicate control proved against it, described in [Explicate control](#explicate-control). The direct proofs also use `Semantics/Graph/Imp.agda`, `LiftLocalsCommon` and `ExplicateCommon`, which are counted in the main rows.

| experiment (not in the totals) | lines |
|---|---:|
| simulation: direct backward simulation for delay — framework | 86 |
| simulation: direct backward simulation for delay — delay | 126 |
| graph model: direct Imp — semantics | 27 |
| graph model: direct Imp — lift locals | 78 |
| graph model: direct Imp — explicate control | 522 |

### Audit-surface counts

The lines a reader must audit to trust each style's theorems (see [Audit surface](#audit-surface)), not in the totals: the shared part (languages, passes, syntax, base types, observations), counted once in the first column, the semantics of each style, and its theorem statements. The machines of Imp, CFG and X86 are read for both the CEK and the reduction statements, so they appear in both semantics rows. The statements of the graph model with errors include its adequacy and end-to-end theorems, so they also read the ISWIM, Clos5 and X86 machines.

| audit surface (not in the totals) | lines | read for denotational: graph model | read for CEK machine + simulation | read for clocked interpreter + value relations | read for reduction semantics + simulation | read for adequacy | read for graph model with errors |
|---|---:|---:|---:|---:|---:|---:|---:|
| languages, compiler passes, syntax, base types (shared) | 1081 | 1022 | 1058 | 1058 | 1081 | 1043 | 1058 |
| graph model: domain, operators, semantics of each language | 412 | 412 | — | — | — | 412 | 135 |
| simulation: small-step machines, transition systems | 693 | — | 693 | — | 299 | 404 | 404 |
| interpreter: clocked interpreters, results | 501 | — | — | 501 | — | — | — |
| reduction: reduction semantics, machines of Imp, CFG and X86, transition systems | 594 | — | 299 | — | 594 | 260 | 260 |
| graph model with errors: domain, error-propagating operators, semantics of each language | 898 | 135 | 404 | — | 260 | 539 | 898 |
| graph model: theorem statements | 70 | 70 | — | — | — | — | — |
| simulation: theorem statements | 54 | — | 54 | — | — | — | — |
| interpreter: theorem statements | 54 | — | — | 54 | — | — | — |
| reduction: theorem statements | 54 | — | — | — | 54 | — | — |
| adequacy: theorem statements | 51 | — | — | — | — | 51 | — |
| graph model with errors: theorem statements | 115 | — | — | — | — | — | 115 |
| **total** | 3739 | **1504** | 1805 | 1613 | 1729 | 1910 | 2071 |

The adequacy statements also use ρ₀ from the denotational ones (`Theorems/Denotational.agda`, 2 lines), not counted in their column.

### Shared modules

| shared module | lines | used by |
|---|---:|---|
| `Compiler.Concretize` | 44 | all four proofs |
| `Compiler.Delay` | 22 | all four proofs |
| `Compiler.Enclose` | 23 | all four proofs |
| `Compiler.EncloseScope` (+ proof/) | 44 | simulation, interpreter, reduction, adequacy, graph model with errors, adequacy with errors |
| `Compiler.Explicate` | 32 | all four proofs |
| `Compiler.Globalize` | 42 | all four proofs |
| `proof.Compiler.GlobalizeTable` | 43 | simulation, interpreter, reduction, adequacy, adequacy with errors |
| `Compiler.LiftLocals` | 36 | all four proofs |
| `Compiler.Optimize` | 55 | all four proofs |
| `Compiler.Pipeline` | 13 | all four proofs |
| `Compiler.PipelineScope` (+ proof/) | 229 | simulation, interpreter, reduction, adequacy, graph model with errors, adequacy with errors |
| `Compiler.RCO` | 110 | all four proofs |
| `Compiler.Select` | 34 | all four proofs |
| `Compiler.Simplify` | 132 | all four proofs |
| `proof.Compiler.SimplifyScope` | 125 | simulation, interpreter, reduction, adequacy, graph model with errors, adequacy with errors |
| `Language.CFG` | 22 | all four proofs |
| `Language.Clos2` | 29 | all four proofs |
| `Language.Clos3` | 26 | all four proofs |
| `Language.Clos4` | 34 | all four proofs |
| `Language.Clos5` | 41 | all four proofs |
| `Language.ISWIM` | 26 | all four proofs |
| `Language.Imp` | 30 | all four proofs |
| `Language.Mon` | 44 | all four proofs |
| `Language.Prim` | 10 | all four proofs |
| `Language.X86` | 45 | all four proofs |
| `Semantics.Observation` | 15 | simulation, interpreter, reduction, adequacy, adequacy with errors |

Shared by all four proofs, and not counted: 21 modules, 850 lines. Counted in the CEK, interpreter and reduction totals and in adequacy: `Compiler.EncloseScope` (44), `proof.Compiler.GlobalizeTable` (43), `Compiler.PipelineScope` (229), `proof.Compiler.SimplifyScope` (125) and `Semantics.Observation` (15), 456 lines. A module marked (+ proof/) is split: its definitions are on the audit surface and its lemmas in `agda/proof/`; the lines are those of both halves. The denotational total counts no shared module. The graph model with errors counts `Compiler.EncloseScope`, `Compiler.PipelineScope` and `proof.Compiler.SimplifyScope` (398), and its adequacy `proof.Compiler.GlobalizeTable` and `Semantics.Observation` (58). Examples, not counted: 215 lines.

### Infrastructure modules

| infrastructure module | lines | used by |
|---|---:|---|
| `Framework.Clocked` (+ proof/) | 243 | interpreter |
| `proof.Framework.GraphModel.Continuity` | 135 | graph model, adequacy, graph model with errors, adequacy with errors |
| `proof.Framework.GraphModel.ContinuityBase` | 99 | graph model, adequacy, graph model with errors, adequacy with errors |
| `Framework.GraphModel.DOpSig` (+ proof/) | 46 | graph model, adequacy, graph model with errors, adequacy with errors |
| `proof.Framework.GraphModel.DenotProperties` | 14 | graph model, adequacy, graph model with errors, adequacy with errors |
| `Framework.GraphModel.Domain` (+ proof/) | 70 | graph model, adequacy, graph model with errors, adequacy with errors |
| `proof.Framework.GraphModel.DomainUtil` | 15 | graph model, adequacy, graph model with errors, adequacy with errors |
| `proof.Framework.GraphModel.DomainUtilBase` | 71 | graph model, adequacy, graph model with errors, adequacy with errors |
| `Framework.GraphModel.Env` (+ proof/) | 84 | graph model, adequacy, graph model with errors, adequacy with errors |
| `Framework.GraphModel.ErrorMonad` (+ proof/) | 935 | graph model with errors, adequacy with errors |
| `proof.Framework.GraphModel.Laws` | 83 | graph model, adequacy |
| `Framework.GraphModel.Ops` (+ proof/) | 324 | graph model, adequacy, graph model with errors, adequacy with errors |
| `Framework.GraphModel.OpsBase` (+ proof/) | 36 | graph model, adequacy, graph model with errors, adequacy with errors |
| `proof.Framework.GraphModel.RenameSem` | 49 | graph model, adequacy, graph model with errors, adequacy with errors |
| `proof.Framework.GraphModel.Semantics` | 82 | graph model, adequacy, graph model with errors, adequacy with errors |
| `proof.Framework.GraphModel.SemanticsCore` | 88 | graph model, adequacy, graph model with errors, adequacy with errors |
| `proof.Framework.GraphModel.SemanticsUses` | 25 | graph model with errors, adequacy with errors |
| `proof.Framework.GraphModel.SemanticsUtil` | 15 | graph model, adequacy |
| `Framework.GraphModel.SetsAsPredicates` (+ proof/) | 56 | graph model, adequacy, graph model with errors, adequacy with errors |
| `proof.Framework.GraphModel.Strict` | 51 | graph model, adequacy |
| `Framework.Iff` | 3 | simulation, interpreter, reduction, adequacy, graph model with errors, adequacy with errors |
| `Framework.ListUtil` (+ proof/) | 114 | graph model, simulation, interpreter, reduction, adequacy, graph model with errors, adequacy with errors |
| `Framework.Primitives` | 17 | graph model, simulation, interpreter, reduction, adequacy, graph model with errors, adequacy with errors |
| `Framework.PrimitivesDec` | 38 | the typed pilot |
| `Framework.Reduction` (+ proof/) | 235 | reduction |
| `proof.Framework.Runs` | 29 | adequacy, adequacy with errors |
| `proof.Framework.Simulation` | 116 | simulation, reduction |
| `Framework.Smallstep` (+ proof/) | 127 | simulation, reduction, adequacy, adequacy with errors |
| `proof.Framework.Syntax.EnvRel` | 15 | simulation |
| `Framework.Syntax.Rename` (+ proof/) | 59 | graph model, simulation, interpreter, reduction, adequacy, graph model with errors, adequacy with errors |
| `Framework.Syntax.Scope` (+ proof/) | 32 | simulation, interpreter, reduction, adequacy, graph model with errors, adequacy with errors |
| `proof.Framework.Syntax.ScopeRename` | 19 | simulation, interpreter, reduction, adequacy, graph model with errors, adequacy with errors |
| `proof.Framework.Syntax.ScopeSubst` | 42 | reduction |
| `Framework.Syntax.SigUtil` | 4 | graph model, simulation, interpreter, reduction, adequacy, graph model with errors, adequacy with errors |
| `Framework.Syntax.Subst` (+ proof/) | 139 | graph model, simulation, interpreter, reduction, adequacy, graph model with errors, adequacy with errors |
| `proof.Framework.Syntax.SubstRel` | 35 | reduction |
| `Framework.Syntax.SyntaxUtil` | 6 | graph model, simulation, interpreter, reduction, adequacy, graph model with errors, adequacy with errors |
| `Framework.Syntax.Uses` (+ proof/) | 44 | graph model, simulation, interpreter, reduction, adequacy, graph model with errors, adequacy with errors |
| `Framework.VecUtil` | 10 | the typed pilot |
| `Framework.abt.AbstractBindingTree` | 14 | graph model, simulation, interpreter, reduction, adequacy, graph model with errors, adequacy with errors |
| `Framework.abt.Fold2` | 19 | graph model, adequacy, graph model with errors, adequacy with errors |
| `Framework.abt.GSubst` | 7 | graph model, simulation, interpreter, reduction, adequacy, graph model with errors, adequacy with errors |
| `Framework.abt.ScopedTuple` (+ proof/) | 129 | graph model, simulation, interpreter, reduction, adequacy, graph model with errors, adequacy with errors |
| `Framework.abt.Sig` | 16 | graph model, simulation, interpreter, reduction, adequacy, graph model with errors, adequacy with errors |
| `Framework.abt.Var` | 14 | graph model, simulation, interpreter, reduction, adequacy, graph model with errors, adequacy with errors |

## What the groups contain

* **shared (counted only in the proofs that use it when not all four do, see above):** the languages (Imp's expressions without control flow are `Simple`, in `Language/Imp.agda`, shared with `Language/CFG.agda`), the compiler passes and their compositions `compile`, `compile-mon`, `compile-imp`, `compile-cfg` and `compile-x86` (`Compiler/Pipeline.agda`), which all four proofs use; the observations and the end-theorem shape (`Semantics/Observation.agda`); and the lemmas about the compiler's output that the operational styles use:
  * `Compiler/EncloseScope.agda`: closed ISWIM programs, and in its proof/ half `enclose-closed` (from `EncloseSim` and `OptimizeSim`);
  * `proof/Compiler/GlobalizeTable.agda`: growing tables `_⊑_`, `glob-grows` and `global-⊑` (from `GlobalizeSim`); the table lookup `global` itself moved to `Language/Clos5.agda`, so the machine and the interpreter use the same one;
  * `Compiler/PipelineScope.agda`: well-scoped Clos5 programs (`Scoped`, the precondition of the operational rco proofs), and in its proof/ half `compile-scoped`, that `compile` produces them from closed ISWIM programs, one lemma per pass (formerly the well-scopedness half of adequacy's `CompileWF`). Only the end-to-end `compile-mon` theorems of the operational proofs use it (and, through them, those of `compile-imp`, `compile-cfg` and `compile-x86`), and the reduction proof's composition, for `optimize-closed` (concretize's precondition).
* **language-independent infrastructure (not counted):** see [Language-independent infrastructure](#language-independent-infrastructure).
  * the abt library (`Framework/abt/`), `Framework/Syntax/SigUtil`, `Framework/Syntax/SyntaxUtil`;
  * `Framework/Syntax/` (lemmas in `proof/Framework/Syntax/`): the syntax of any signature and the lemmas about it, `Rename.agda` (`rename-cong`, `rename-fuse`, `rename-id`, from `DelaySim`), `Scope.agda` (well-scoped terms and `ws-uses`, from `OptimizeSim`), `ScopeRename.agda` (renaming preserves well-scopedness, formerly adequacy's `Scope`), `Uses.agda`; and `ListUtil.agda`, lookup in an environment, projection from a tuple, and lemmas about lookups, also in reversed and replicated lists (formerly `Operational/Machine/Common.agda`, plus list lemmas from `ConcretizeSim` and `GlobalizeSim`, and from adequacy);
  * `Framework/Primitives.agda` (base types) and `Framework/Iff.agda` (`_⇔_`);
  * the denotational framework: sets as predicates, environments, DOp signatures, `abt.Fold2` (`Framework/GraphModel/`, `Framework/abt/`), and in `proof/Framework/GraphModel/` the semantics of any signature and its monotonicity (`Semantics`, formerly `NewSemantics`, which also gives consistency), monotonicity and consistency of operators (`DenotProperties`), `RenameSem`;
  * the graph model, `Framework/GraphModel/`, in three groups (since PR #50): (a) values and consistency (`Domain`), the operators the two models share unchanged (`OpsBase`: constants and the components of a tuple of results), the machinery for any operators (`ContinuityBase`: finite approximations, `Continuous`, `Good`) the properties of whole terms of any graph-model semantics (`SemanticsCore`: term continuity, `GoodSemantics`) and facts about values (`DomainUtilBase`: tags, depth, flat values); (b) the graph model's operators (`Ops`), their continuity (`Continuity`), their β laws on terms (`SemanticsUtil`), facts about them (`DomainUtil`), and, since PR #51, operators strict in their operands (`Strict`) and the let/case and strict-write laws (`Laws`); (c) the error monad of the graph model with errors, its operators (the graph model's operators under binds) and their laws (`ErrorMonad`, since PR #53; before, `ErrorOps`, `ErrorContinuity`, `ErrorStrict` and `ErrorLaws`), used only by the graph model with errors and its adequacy;
  * the small-step framework (`Framework/Smallstep.agda`: transition systems and the iff end theorem; `proof/Framework/{Smallstep,Simulation}.agda`: lemmas about runs, forward simulation, backward from forward plus determinism) and the clocked one (`Framework/Clocked.agda`: results with timeout, the clocked end theorem; `proof/Framework/Clocked.agda`: `clocked`), both parameterized over the type of observations;
  * the reduction framework (`Framework/Reduction.agda`: a reduction as a step function with congruence rules, `step-in`, and its machine; `proof/Framework/Reduction.agda`: frames, how a target term answers a source term's reduction, congruence, and the end theorem), and the substitution library (`Framework/Syntax/Subst.agda`: substitution for any signature; `proof/Framework/Syntax/{Subst,ScopeSubst,SubstRel}.agda`: the σ-calculus fusion lemmas, scoping, and the closure of a relation on terms under renaming and then substitution). They are used only by the reduction proof.
* **semantics of the languages:**
  * denotational: the meaning of this compiler's primitives (`Semantics/Graph/Prim.agda`: `out`, `primD` and its lemmas), the semantics of ISWIM, Clos2 through Clos5, Imp, CFG and X86, plus their monotonicity and consistency and the continuity instances the proofs use (in `proof/Semantics/Graph/`; for Clos5, `proof/Semantics/Graph/Clos5IswimContinuous.agda`, used by rco, lift locals and adequacy). For Imp: `Semantics/Graph/Imp.agda` (stores, slots, the frame check, atoms, simple expressions, frames and tables, also used by CFG and by the direct semantics) and the continuation-passing semantics `Semantics/Graph/ImpK.agda`; the direct one, `proof/Semantics/Graph/ImpDirect.agda`, is an experiment;
  * Simulation: the eight machines (ISWIM, Clos2–Clos5, Imp, CFG and X86), and the small-step framework at this compiler's observations (`Semantics/CEK/Smallstep.agda`, which keeps the design note, with its proof/ half, and `proof/Semantics/CEK/Simulation.agda`);
  * Interpreter: the eight clocked interpreters (Clos5's, Imp's, CFG's and X86's take the table of global definitions), and the clocked framework at this compiler's observations (`Semantics/Interp/Clock.agda`, with its proof/ half);
  * Reduction: the five reduction semantics (ISWIM, Clos2–Clos5, `Semantics/Reduction/`), with their values in their proof/ halves, the framework instance (`Semantics/Reduction/Smallstep.agda`), and the machines of Imp, CFG and X86 with the values they share (`Semantics/CEK/Values.agda`) and the small-step instances, which are the CEK column's and are counted in both.
* **one row per pass:** that pass's correctness proof. The rco row also contains the end-to-end theorem for `compile-mon`, a corollary of the composition and the rco theorem (11 lines in the denotational proof, 2 in each operational one), in all four styles; likewise the lift-locals row contains the end-to-end theorem for `compile-imp`, and, in the denotational and interpreter proofs, the explicate-control row the one for `compile-cfg` and the select-instructions row the one for `compile-x86` (in the CEK and reduction proofs, which share those two passes, these two are in the composition row: `CompilerX86Sim`, `CompilerX86Red`). The denotational lift-locals and explicate-control rows include the modules both semantics of Imp use (`LiftLocalsCommon`, `ExplicateCommon`).
* **composition:** the end-to-end theorem built from the per-pass results. The compiler `compile` itself is shared (`Compiler/Pipeline.agda`), so neither operational proof imports the denotational one.
* **shared modules not used by all four proofs:** see [Shared modules](#shared-modules).
* **simplify:** the pass (`Compiler/Simplify.agda`) is shared, as every pass is; its syntactic lemmas (`proof/Compiler/SimplifyFacts.agda`), which all four proofs use, are counted in the simplify row of every column (a group of all four, as the 'op+red' groups are of two); that it keeps programs closed (`proof/Compiler/SimplifyScope.agda`) is a shared module that only the operational compositions and adequacy use. See [Simplify](#simplify).

## Caveats

* **The theorems differ.** The simulation, interpreter and reduction theorems have the same shape. They are stronger than the denotational one: they separate errors from divergence. In the graph model, both denote ∅.
* **Terminology: "error".** An error (the observation `o-error`, the `error` result of an interpreter or of `red`) is a *trapped* error in the sense of Cardelli ("Type Systems"): the program stops and the semantics reports it. Every operational semantics here is a total step or eval function, so no program can get stuck, which would be an *untrapped* error; a term that `red` cannot reduce is reported as an error. (Before this, the code said "wrong", after Milner, which in Cardelli's terms usually means an untrapped error.) The graph model does not distinguish errors from divergence: both denote ∅. The graph model with errors, using ω, does, for the whole compiler; see [Graph model with errors](#graph-model-with-errors).
* **Determinism.** The simulation and reduction proofs rely on every machine and reduction being deterministic and total. The backward direction of each pass comes from forward simulation plus determinism, and the framework proves that once. The interpreter proof needs no determinism argument: an interpreter is a function, and every pass but simplify is proved clock for clock (see below); simplify's clock-monotone proof uses the interpreter's monotonicity in the clock instead.
* **Why "backward = forward + determinism" has no denotational counterpart.** Consistency of denotations plays the role of determinism. Take c ∈ ⟦pass M⟧ and suppose ⟦M⟧ has an element.
  * If it is a constant c′, the forward direction puts c′ in ⟦pass M⟧, and consistency forces c = c′.
  * If it is a function, tuple or sum, consistency rules out c.

  That leaves ⟦M⟧ = ∅, and showing that ⟦pass M⟧ = ∅ too is a reflection argument. A forward relation cannot carry absence.

  This is inherent in a continuous semantics. Every element of a denotation is a finite observation, evidence available after finitely much computation. Termination with a result is a finite observation; divergence is not, since no finite evidence shows that a program diverges. So divergence can only appear as the absence of elements, and an element marking divergence would make the semantics non-monotone. The simulation proof avoids this because its divergence is an infinite run, a coinductive object that forward simulation maps to another infinite run.

  Adding an error element to the graph model would not change this. It would make an error a finite observation, handled by the forward direction plus consistency, but ∅ would still mean divergence and would still have to be reflected. Avoiding the reflection would take a coinductive semantics, such as the delay monad or traces, and that gives up the finite-observation style.

  The cost falls only on passes that change representation. When ⟦pass M⟧ ≃ ⟦M⟧ (enclose, optimize, concretize, globalize, rco, lift locals, explicate control), both directions come from the equation at once, with no determinism argument.
* **Machines.** The ISWIM, Clos2 and Clos3 machines check that an operator is a function before evaluating the argument. Delay needs this to preserve errors: it takes the closure apart with `fst` before the argument. The Clos4 and Clos5 machines check that the operator is code only at the call, after all three operands, like an indirect call instruction, so that rco, which let-binds all the operands before the call, preserves errors. On delay's output the late check always passes, since a non-closure has already stopped with an error at `fst`.

* **Binders bind only consistent sets.** In the graph model, Λ and 𝒞 bind only finite sets that are consistent, so a denotation under a consistent environment has no inconsistent elements. This was needed for explicate control: with binders that admit any finite set, ⟦explicate P⟧ ≃ ⟦P⟧ is false (see [Explicate control](#explicate-control)). It cost 96 denotational lines and 74 adequacy lines when it was made, and saved 16 in delay, whose own consistency induction gave way to a generic one: the monotonicity proof of the denotational framework now works for any relation the operators preserve, so the consistency of each semantics comes from its operator lemmas. Where a proof picks a finite part of a set for a binder (concretize, delay in both directions, rco's let-β), it needs that set consistent, so those proofs take a consistent environment.
* **Two denotational semantics of Imp.** The main rows use a continuation-passing semantics of Imp (`Semantics/Graph/ImpK.agda`); a direct one (`proof/Semantics/Graph/ImpDirect.agda`), with lift locals and explicate control proved against it, is kept as an experiment. Choosing the semantics is part of the proof effort, as choosing the machines or interpreters is for the operational styles; the CPS one is the better effort for this pass sequence. See [Explicate control](#explicate-control).
* **Clos5 continuity is denotational.** The continuity of the Clos5 semantics in the environment (117 lines then, 118 now), formerly adequacy's `Clos5Continuous`, is now `proof/Semantics/Graph/Clos5IswimContinuous.agda`, in the denotational row "semantics of the languages", because the rco proof uses it (for the let laws), as does lift locals. Adequacy reuses it from there and does not count it again; adequacy's Clos5 row shrank by the same 117 lines.
* **The rco preconditions differ.** The denotational rco theorem is an equation with no precondition on programs; the three operational ones (CEK, interpreter, reduction) need `Scoped`, and their end-to-end `compile-mon` theorems therefore pay for `compile-scoped` (249 lines, in the shared row, plus `Syntax/ScopeRename`, now infrastructure). See [Remove complex operands](#remove-complex-operands).
* **The reduction proof's concretize needs a well-scoped program** (`WS 0`), which the CEK and interpreter proofs do not: a variable of a closure's code beyond its parameters becomes, in Clos2 and in Clos3, two different variables, which substitution then moves differently, while the machines look both up in the closure's environment, where both fail. The compiler's composition discharges it with `optimize-closed` (shared, `Compiler/PipelineScope`). See [Reduction semantics + simulation](#reduction-semantics--simulation).
* **The small-step framework answers a stop by a run.** A forward simulation now may answer a source that stops with a target run to a final state (`runs`, not only `stops`): a reduction target often has administrative steps left (a projection, a let, the evaluation of an atom) when the source errors or reaches a value. The end theorem still follows by determinism (`final-unique`, +9 lines of infrastructure); the CEK proofs do not use it.
* **Lift locals and explicate control need no precondition in any style.** A variable out of scope becomes a slot beyond the frame, which errors (operationally) or reads as `init` (denotationally) exactly where the Clos5 variable does. Assigning a slot beyond the frame errors in all four styles (∅ denotationally, since explicate control; see [Explicate control](#explicate-control)). See [Lift locals](#lift-locals).
* **Select instructions: a precondition only in the denotational proof.** The denotational theorem assumes every global definition has at least 2 locals (`select-correct`), discharged for compiled programs; neither operational one has a precondition. See [Select instructions](#select-instructions).
* **Adequacy reaches X86, the final target, but not the intermediate languages.** Adequacy, and so a statement about running code, exists for ISWIM, Clos5 and X86: the end-to-end theorem for `compile-x86` relates the ISWIM machine to the X86 machine (`end-to-end-x86-const`, `end-to-end-x86-converges`). The end-to-end denotational theorems for `compile-mon`, `compile-imp` and `compile-cfg` still speak only about the denotations of Clos5, Imp and CFG. X86 adequacy has preconditions that compiled programs satisfy, discharged by `compile-x86-wf` (see [Adequacy for X86](#adequacy-for-x86)); like Clos5's, it cannot tell an error from divergence.

## Audit surface

The development is split, as in jsiek/AI-for-pl, into what must be read to trust the results and what Agda has checked (see `agda/README.md`):

* **the theorem statements**, `agda/Theorems/{Denotational,Simulation,Interpreter,Reduction,Adequacy}.agda`: each public theorem with its full type, defined as the theorem of `agda/proof/` (`enclose-correct = EncloseCorrect.enclose-correct-closed`), so Agda checks that the statement is the type of the proof;
* **the definitions they use**, everything else outside `agda/proof/`: the languages and passes (`agda/Language/`, `agda/Compiler/`), the semantics of each style (`agda/Semantics/Graph/`, `agda/Semantics/CEK/`, `agda/Semantics/Interp/`, `agda/Semantics/Reduction/`, `agda/Semantics/Observation.agda`), and the language-independent definitions in `agda/Framework/` (the abt extract, syntax and substitution, the graph model's sets, values and operators, the small-step, reduction and clocked frameworks);
* **`agda/proof/`**, mirroring the paths of the surface: all proofs, and the lemmas of every module that mixed definitions and lemmas (`agda/X.agda` keeps the definitions, `agda/proof/X.agda` re-exports them with the lemmas).

`loc.py` checks that no module of the surface imports one of `agda/proof/` (the theorem files excepted) and that every module outside `agda/proof/` is reached from the theorem files, so the surface is exactly the closure of the statements, at the granularity of modules. Two choices keep it small:

* **Restricted statements.** Adequacy for the Clos5 and X86 machines is proved for any well-formed program, but the well-formedness conditions (references only to older definitions, slots within the frame, a consistent table: `Clos5WF`, `X86WF` and `RB` of `GlobalizeCorrect`, about 60 lines) are proof-internal, so `Theorems/Adequacy.agda` states it for the programs the compiler produces (`compile M`, `compile-x86 M` for a closed `M`), discharging well-formedness with `compile-wf` and `compile-x86-wf`. Soundness and adequacy are stated as their characterizations (`const-iff`, `nonempty-iff`, `error-empty`, `diverges-empty`), so `ShapeOf` stays in `agda/proof/`. The denotational `select-correct` states its precondition inline (`All (λ b → 2 ≤ Body.locals b) (defs P)`), and `ρ₀` is defined in `Theorems/Denotational.agda` (the proofs use a definitionally equal one, in the graph model's `Domain`).
* **Semantics without their monotonicity.** The generic `Semantics` record of the graph model carries a monotonicity proof, so a semantics built with it would put the monotonicity of every operator on the surface. Instead the surface defines the meaning of ISWIM and Clos2–Clos4 directly as the fold of their operators (as Clos5's already was); `agda/proof/` builds the `Semantics` instance, whose `⟦_⟧` is that fold by definition, and the proofs are unchanged.

**What it changed in the totals.** Without import statements, which are no longer counted (see below), the split costs the denotational total 21 lines (2921 → 2942), the simulation one 4 (2904 → 2908), the interpreter one 4 (2058 → 2062) and adequacy 3 (3165 → 3168): the direct definitions of the semantics on the surface, the module lines of the new proof halves, and their `open … public` re-exports. Counting imports, as when the split was made, the totals count the two halves of a split module as one module, so only the module headers and imports of the new proof halves, and the direct definitions of the semantics, add lines: the denotational total +80 (semantics row: `Prim` +12, `Sem/ISWIM` +14, `Sem/Clos2Iswim` +20, `Sem/Clos3Iswim` +17, `Sem/Clos4Iswim` +17), the simulation one +17 (semantics row +5 for the proof halves of `Operational/{Smallstep,Simulation}`; shared row +12, for `EncloseScope` +5 and `PipelineScope` +7), the interpreter one +16 (semantics row +4 for `Functional/Clock`; shared row +12), and adequacy +12 (shared row). No per-pass row changed. The infrastructure table changed likewise (1693 → 1788, the proof halves of the framework modules, and `Equivalent` moved from `Simulation` to `Smallstep`). The theorem files (368 lines with imports, 221 without) are new boilerplate and are not in the totals; they are in the audit-surface table.

**Legacy top-level files.** `NewDenotProperties`, `NewDOpSig`, `NewEnv`, `NewSemantics`, `NewSigUtil`, `NewSyntaxUtil`, `Primitives`, `SetsAsPredicates` and `RenameSem` were not dead: the compiler's closure uses all of them. `agda/old/` has its own copies of all but `RenameSem` (it is checked from `agda/old/`, with the external abt library), so it does not depend on them. They moved, with the abt extract, `GraphModel/`, `Syntax/`, `ListUtil`, `Iff` and the small-step and clocked frameworks, under `agda/Framework/` (definitions) and `agda/proof/Framework/` (lemmas), renamed without the `New` prefix (`SigUtil`, `SyntaxUtil`, `GraphModel/{DOpSig,Env,Semantics,DenotProperties}`).

## History

| date | change | denotational: graph model | CEK machine + simulation | clocked interpreter + value relations | reduction semantics + simulation |
|---|---|---:|---:|---:|---:|
| 2026-10-11 | first complete versions (PR #14) | 4251 | **2134** | — | — |
| 2026-10-11 | leaner delay proof (PR #15) | 3725 | **2134** | — | — |
| 2026-10-11 | dead code, consistency, shared lemmas (PR #16) | 2836 | **2134** | — | — |
| 2026-10-11 | delay relation without visible fuel, Calls as a predicate (PR #17) | 2825 | **2134** | — | — |
| 2026-10-11 | joined pairs ⦅ u , v ⦆ instead of the halves ⦅ u ∣ and ∣ v ⦆ (PR #18) | 2823 | **2134** | — | — |
| 2026-10-11 | simulation proof cleanup: framework specialised to step-function machines, end theorems composed instead of simulations, no per-pass corollaries, shared `uses-bound`, pruned imports (PR #20) | 2811 | **1862** | — | — |
| 2026-10-11 | interpreter proof pilot: clocked interpreters for all five languages, enclose clock for clock | 2811 | 1862 | **541** | — |
| 2026-10-11 | interpreter proof complete: all five passes clock for clock, composition (`CompilerFuel`); machine-independent lemmas and observations moved to shared modules, so neither operational style imports the other (PR #21) | 2811 | 1626 | **1130** | — |
| 2026-10-11 | `compile` moved from `CompilerCorrect` to the shared `Compiler/Pipeline.agda`, so no operational proof imports the denotational one; dead imports of the denotational infrastructure removed from the languages (PR #24; old method) | 2804 | 1626 | **1130** | — |
| 2026-10-11 | the same code, new method: shared modules not used by all three proofs counted in each proof that uses them (PR #24) | 2832 | 1783 | **1287** | — |
| 2026-10-11 | arithmetic: sub and eq (PR #25) | 2935 | 1933 | **1407** | — |
| 2026-10-11 | late code check in Clos4/Clos5 (PR #26) | 2935 | 1926 | **1404** | — |
| 2026-10-11 | remove complex operands, all three proofs; Clos5 continuity to the denotational side, scoping of `compile` to the shared code (PR #26) | 3289 (+354) | 2653 (+727) | **1980** (+576) | — |
| 2026-10-12 | lift locals into Imp, all three proofs (PR #27) | 3551 (+262) | 2967 (+314) | **2184** (+204) | — |
| 2026-10-12 | explicate control into CFG, all three proofs, the denotational one against the direct semantics of Imp; binders bind only consistent sets (PR #28) | 4323 (+772) | 3181 (+214) | **2365** (+181) | — |
| 2026-10-12 | continuation-passing semantics of Imp for the denotational lift locals and explicate control, the direct one an experiment; what both have in common factored out (PR #28) | 3989 (−334) | 3181 | **2365** | — |
| 2026-10-12 | the same code, new method: language-independent infrastructure in a separate table, not counted (PR #28) | 3113 | 2935 | **2224** | — |
| 2026-10-12 | select instructions, all three proofs (PR #29) | 3537 (+424) | 3325 (+390) | **2463** (+239) | — |
| 2026-10-12 | clocked interpreters in do-notation (cosmetic; PR #30) | 3537 | 3325 | **2463** | — |
| 2026-10-12 | X86 machine and interpreter aligned with the X86 semantics at calls; adequacy for X86, end to end for `compile-x86` (PR #33) | 3537 | 3328 (+3) | **2461** (−2) | — |
| 2026-10-12 | audit surface split: the theorem statements in `agda/Theorems/`, the definitions they use outside `agda/proof/`, the proofs and the lemmas of split modules in `agda/proof/` (PR #35) | 3617 (+80) | 3345 (+17) | **2477** (+16) | — |
| 2026-10-12 | the same code, new method: import statements not counted (PR #35) | 2942 | 2908 | **2062** | — |
| 2026-10-12 | the same code, regrouped for a fourth column: the values of the Clos5 machine to `Semantics/CEK/Values.agda`, `‼-map` to `ListUtil` (infrastructure), the compositions into CFG and X86 out of `ExplicateSim` and `SelectSim` (`CompilerX86Sim`), shared modules counted unless all four proofs use them (PR #37) | 2942 | 2906 | **2062** | — |
| 2026-10-12 | reduction semantics + simulation, every pass; explicate control and select instructions shared with the CEK column (PR #37) | 2942 | 2906 | **2062** | 3011 |
| 2026-10-13 | simplify (ISWIM → ISWIM), a cp0-style source optimizer, as the first pass of `compile`, all four proofs; that simplify keeps programs closed for the operational compositions (`SimplifyScope`, shared, 110); the continuity of ISWIM from adequacy to the denotational semantics row (44); in the infrastructure `equiv-sym` (+5), `clocked-le` (+54) and `ws-bound` (+10) (PR #40) | 3349 (+407) | 3578 (+672) | **2863** (+801) | 3734 (+723) |
| 2026-10-13 | simplify's CEK and interpreter proofs trimmed: one description of values for terms and known values (`Desc`, strong for terms, up to functions for known values), the shift of a small value from that of a description, one lemma for a variable bound in both environments (`ok-bind`), shared helpers in the interpreter's backward direction (PR #40) | 3349 | 3558 (−20) | **2840** (−23) | 3734 |
| 2026-10-13 | inlining in simplify (transformation 5): a known function is kept as its source body with its `Facts`, and a call of it is replaced by its body simplified at the call, the operand bound as in β (a let when it is not a value), when the result is small enough, under fuel; copy propagation keeps what is known of a copied variable; β and inlining share one lemma per proof (PR #41) | 3360 (+11) | 3607 (+49) | **2900** (+60) | 3821 (+87) |
| 2026-10-13 | infrastructure audit, step 1: language-independent lemmas that the proofs repeated defined once in the infrastructure (list lookups, the graph model's `ρ₀`, `ne-mem` and `Λ-≃`, the continuity of Clos5 from `SemanticsUtil`, the environment lemmas `•-~` and `extend-nonempty-env` for local copies, adequacy's runs from any state and `terminates-det`); the infrastructure +59 (1866 → 1925), of which each proof reaches +28, +18, +16 and +18; adequacy 3246 → 3208 (PR #42) | 3299 (−61) | 3581 (−26) | **2892** (−8) | 3810 (−11) |
| 2026-10-13 | `let` in ISWIM, Clos2 and Clos3 (semantics in every style, every pass, every proof); simplify emits `let x = M' in N'` where it left the redex `(λ x. N') M'`, and simplifies a source `let` like β (PR #43; see [Adding let](#adding-let-to-iswim-clos2-and-clos3)) | 3393 (+94) | 3639 (+58) | **2933** (+41) | 3904 (+94) |
| 2026-10-13 | infrastructure audit, interpreter track: the `Result` monad laws, clock monotonicity (`⊑-bind`, `Stable`, `Back`, `clocked-back`) and `clocked-≡` move into `Framework.Clocked` (132 → 243) (PR #44) | 3393 | 3639 | **2794** (−139) | 3904 |
| 2026-10-13 | infrastructure audit, CEK track: `step⁺`, `Reach`/`after`, `Lag`, `answers-at` and `next?` in the small-step framework (188 → 243), renamed environments in `Syntax.EnvRel` (15); the reduction column shares the Imp machine and the explicate and select proofs (PR #45) | 3393 | 3526 (−113) | **2794** | 3897 (−7) |
| 2026-10-13 | infrastructure audit, reduction track: `ret?`, operand lists (`Each`, `ans-cons`), `ret?-ans`, let chains and the one-value substitution `≈-[]` in the reduction framework (130 → 235) and the substitution lemmas (PR #46) | 3393 | 3526 | **2794** | 3689 (−208) |
| 2026-10-13 | infrastructure audit, graph-model track: each operator's monotonicity, consistency and continuity proved once (`Good`), and each language's semantics built from a table of operators (semantics row 744 → 447); congruences from monotonicity (`mono⇒≃`); β laws for any continuous semantics (`Λ-β`, `let-β`, `clos-β`); domain facts in `DomainUtil`; graph model values, operators, continuity 454 → 836 (PR #47) | **2744** (−649) | 3526 | 2794 | 3689 |
| 2026-10-13 | closure-conversion passes labelled "CC: " in the tables; no count changes (PR #48) | **2744** | 3526 | 2794 | 3689 |
| 2026-10-13 | graph model with errors, a pilot (ISWIM, Clos2–Clos4; simplify, enclose, concretize, delay, adequacy for ISWIM; optimize owed), not in the totals: delay 1037 lines against 594; the graph model's infrastructure split into what any graph-model semantics uses and its operators (+13 module lines, 1749 → 1762; adequacy's 1959 → 1972) (PR #50) | **2744** | 3526 | 2794 | 3689 |
| 2026-10-13 | graph model with errors for the whole compiler: semantics of Clos5, Imp, CFG and X86 that err where their machines do; optimize, globalize, rco, lift locals, explicate control, select and the composition; adequacy for the Clos5 and X86 machines and the end-to-end theorems on errors, constants, answers and divergence. A fifth column, not in the comparison: 3953 lines (adequacy 4760, infrastructure reached 2670); none of the four totals changes (PR #51) | **2744** | 3526 | 2794 | 3689 |
| 2026-10-13 | one infrastructure rule for both graph models: laws over the operators are infrastructure. The graph model's strict operators (from rco), let/case and strict-write laws (from lift locals and select) move to `Strict` and `Laws`, and `strict`, `payloadD` to `Ops`: rco 168 → 118, lift locals 214 → 142, select 281 → 271, semantics 447 → 443; its infrastructure 1762 → 1900 (adequacy's 1972 → 2110). The errors model is unchanged (PR #51) | **2608** | 3526 | 2794 | 3689 |
| 2026-10-13 | graph model with errors, monadic (pilot): the error-propagating operators of ISWIM and Clos2 rebuilt from an error monad on 𝒫 Value, with the graph model's operators as kernels; simplify, enclose and ISWIM adequacy on it. Not in the totals: semantics of ISWIM and Clos2, simplify and enclose 827 lines against 881 in the errors model, ISWIM adequacy 795 against 915, error-specific infrastructure 409 against 685 for the same operators; none of the totals changes (PR #53) | **2608** | 3526 | 2794 | 3689 |
| 2026-10-13 | graph model with errors, monadic (pilot), step 1: Clos3 and Clos4 on the monad (pairs, the late-checked call), concretize and delay; a cleanup of the step-0 proofs (one `Val` predicate, β laws stated with it, `binds-good`, `clos-β`, `⟦⟧-closed₀`). Not in the totals: delay 901 lines against 1037 in the errors model (594 in the graph model), concretize 134 against 151, simplify 351 (was 385) against 380, enclose 92 (was 108) against 109, ISWIM adequacy 790 against 915, error-specific infrastructure 564 against 997 for the same four languages; the denotational framework row grows by 3 (`⟦⟧-closed₀`); none of the totals changes (PR #53) | **2608** | 3526 | 2794 | 3689 |
| 2026-10-13 | graph model with errors rebuilt on the error monad for the whole compiler, replacing the old development (PR #53, step 2): Clos5, Imp, CFG and X86 semantics on the monad; optimize, globalize, rco, lift locals, explicate control, select and the composition; adequacy for the Clos5 and X86 machines. The errors column: passes and semantics 3953 → 3528 (delay 1037 → 898, rco 206 → 194, select 349 → 363, lift locals 129 → 138; Clos2Continuous, unused, dropped), adequacy 4760 → 4333 (Clos5 1153 → 904, X86 2149 → 2096), error-specific infrastructure 1317 → 935, now sharing 474 lines of the graph model's operators; no other total changes | **2608** | 3526 | 2794 | 3689 |
| 2026-10-13 | typed intermediate languages, a pilot (ISWIM → Clos4; not in the totals): cast insertion into intrinsically typed ISWIMᵀ–Clos4ᵀ (closures in Clos4ᵀ packed as ∃ n. code n × tup n), typed enclose, concretize and delay, in the CEK and graph-with-errors columns; the CC passes shrink (CEK enclose 188 → 106, concretize 182 → 115, delay 134 → 101; graph model with errors enclose 90 → 38, concretize 134 → 69) but not delay in the graph model with errors (898 → 919), and cast insertion costs 195 / 122; the segment, without optimize, CEK 1032 → 1083, graph model with errors 1541 → 1741. New infrastructure 48 (3756 → 3804); see [Typed intermediate languages (pilot)](#typed-intermediate-languages-pilot) | **2608** | 3526 | 2794 | 3689 |

**Infrastructure audit, step 1 (PR #42).** The last row moves language-independent reasoning that the proofs had repeated, or had written locally, into the infrastructure, under the policy of [Language-independent infrastructure](#language-independent-infrastructure). No theorem statement, pass or semantics changed. What moved:

* **List lookups** (`proof/Framework/ListUtil.agda`, 98 → 114): `‼-pw`, lookup in pointwise-related lists (it was in `RCOFuel`, `LiftLocalsSim` and `LiftLocalsRed`, and as `lookup-pw` in `GlobalizeSim` and `GlobalizeFuel`); `reverse-map-‼`, lookup in the reverse of a mapped list (the tables of rco, explicate control and select instructions in the CEK and reduction proofs); `‼-any` (`RCOSim`, `RCORed`); and `args→list-hom`, listing the subterms of a tuple after a map over them, given its defining equation, which replaces `enc-list`, `opt-list`, `conc-list` and `simps-list` in the CEK proofs (`del-args` is a pointwise relation, not a map, and is kept).
* **Graph model:** `ρ₀`, the environment of a closed program (`Domain`; it was in `DelayFiniteCommon` and `SimplifyCorrect`), `ne-mem` (`SetsAsPredicates`; `DelayFiniteCommon`, `RCOCorrect`) and `Λ-≃` (`Ops`; word for word in `SimplifyCorrect` and `RCOCorrect`). `Clos5IswimContinuous` instantiates `SemanticsUtil` for `args-nth-mono`, `args-nth-cont` and `term-continuous` instead of repeating them (the semantics row, 734 → 716). Local copies of the environment lemmas `•-~` (`part` in `SimplifyCorrect`, `rel-ext` in `GlobalizeCorrect`, an extension in `RCOCorrect`) and `extend-nonempty-env` (five in `DelayPreserve` and `DelayReflectFinite`) were replaced by them.
* **Adequacy:** the runs of a step function from any state (`_↠_`, `_++↠_`, `↠-final-det`, formerly `Common.Runs`) are `proof/Framework/Runs.agda` (29 lines, used only by adequacy), and `terminates-det`, that a machine terminates with at most one observation, is proved once in `proof/Framework/Smallstep.agda` from `final-unique` (2 lines) instead of in the ISWIM and Clos5 adequacy proofs (ISWIM 684 → 651, Clos5 717 → 712).

The totals went down by 61, 26, 8 and 11 lines (graph model: semantics −18, simplify −12, delay −15, globalize −3, rco −13; CEK: 3 or 4 in each of seven rows; interpreter: globalize and rco −4 each; reduction: rco −7, lift locals −4), and adequacy by 38. The infrastructure grew by 59 lines (1866 → 1925): list lookups +16, the denotational framework +3, the graph model +9, the small-step framework +2, runs +29. Since the counts are by module, each proof is shown reaching all of a module it imports: the graph model reaches +28 lines of infrastructure (1310 → 1338), the CEK proof +18 (783 → 801), the interpreter +16 (729 → 745), the reduction proof +18 (967 → 985), and adequacy +59 (1462 → 1521).

**A fourth column (PR #37).** The last two rows. The first is the CEK code regrouped so that the reduction column can share the machines of Imp, CFG and X86 and the proofs of explicate control and select instructions: the values of the Clos5 machine, which the Imp and X86 machines use, moved to their own module (+1 line, the module line, in the semantics row: 656 → 657), the list lemma `‼-map` from `RCOSim` to `ListUtil` (rco 414 → 410), and the end-to-end theorems for `compile-cfg` and `compile-x86` from `ExplicateSim` and `SelectSim` to `CompilerX86Sim` (explicate control 129 → 127, select instructions 240 → 238, composition 19 → 24); in all 2908 → 2906. The infrastructure grew by 344 lines: the substitution library (189 with `ScopeSubst` and `SubstRel`) and the reduction framework (130), used only by the reduction column, and in the shared infrastructure the `runs` answer of the small-step framework (+9) and three list lemmas (+16). See [Reduction semantics + simulation](#reduction-semantics--simulation).

**Import statements (PR #35).** The last two rows are the same code counted two ways: from PR #35 on, import statements are not counted. With them, the split into an audit surface and `agda/proof/` cost the denotational total 80 lines, 61 of them module lines and imports of the new proof halves; reducing them would have needed re-export modules that add dependencies between files, or merged modules. Imports measure how finely a development is divided into modules more than what it proves, and the denotational proof is divided most finely: imports were 19% of its total, against 13% and 17% for the simulation and interpreter ones. Without them the totals go from 3617, 3345 and 2477 to 2942, 2908 and 2062 (−675, −437, −415), adequacy from 3719 to 3168, and the infrastructure from 1788 to 1453. The counts in the sections below are as of their PRs, with imports.

**Adequacy for X86 (PR #33).** The X86 machine and interpreter now do what the X86 semantics says at calls (see [Select instructions](#select-instructions)): the callee starts with `%rax` unset and no flag, `callq` goes wrong if `%rdi` or `%rsi` is unset, and `retq` goes wrong if `%rax` is unset, also when it returns to a caller. This cost the machine semantics 3 lines (the machine) and saved the interpreter select proof 2 (its hypothesis on calls lost the registers); `SelectSim` and `SelectFuel` still need no precondition. Adequacy went from 2187 to 3707 lines: X86 +1243, well-formedness 60 → 328, end to end 24 → 39, ISWIM +2 and Clos5 −8 (the runs of any machine are now shared, `Common.Runs`, and the Clos5 machine's values, which X86 shares, are in `Values.agda`, used by both); the list lemmas it needed went to `ListUtil` (infrastructure, 62 → 92 lines, also used by Clos5 adequacy).

The last two PR #28 rows are, apart from moving modules, the same code counted two ways. The infrastructure was split from the compiler (the graph model's values, consistency and operators from `Compiler/Model/Graph/Domain/ISWIM/` to `GraphModel/`, leaving only the meaning of the primitives, `Semantics/Graph/Prim.agda`; `Sem/Continuous` to `GraphModel/SemanticsUtil`, `Sem/RenameSem` to `RenameSem`; the syntax lemmas from `Compiler/Lang` to `Syntax/`; the small-step and clocked frameworks parameterized over the type of observations, with instances at this compiler's observations left in `Compiler/`), and the infrastructure left the totals. The rows "generic infrastructure" (307, 188, 80) and "domain, operators, continuity" (511, denotational only) are gone, and so are the shared modules that became infrastructure (`abt.Fold2`, 28, from the denotational total; `Syntax.Scope` and `Syntax.ScopeRename`, 61, from both operational totals); `Observation` shrank from 26 to 23 lines (`_⇔_` to `Iff`, `SameObs` unfolded in the frameworks). The semantics rows went from 782, 629, 461 to 743, 635, 464 (the denotational one gaining `Prim.agda`, the operational ones the instances of their frameworks), and the denotational pass rows changed by 1 to 3 lines each (imports). In all −876, −246 and −141. What each proof relies on now appears in the infrastructure table (1331, 676 and 569 lines). Adequacy went from 2172 to 2246 with the consistent binders (ISWIM 798 → 850, Clos5 847 → 869), and from 2246 to 2187 with the new method (ISWIM 853, Clos5 871, shared 443 → 379).

The two PR #24 rows are the same code counted two ways. Before, every shared module was left out of all totals, although four of them (157 lines) are used only by the two operational proofs and adequacy, and one (`abt.Fold2`, 28 lines) only by the denotational proof and adequacy; now these count in each proof that uses them (+28, +157, +157), and adequacy grows from 1981 to 2138. Moving `compile` took 7 lines from the denotational composition (the definitions and their imports); the shared code went from 1071 to 1069 lines (+13 for `Pipeline`, −15 for the dead imports).

PR #16 also changed the grouping: the shared counts now include `Primitives`, `NewSigUtil` and `NewSyntaxUtil`, and `ISWIMContinuous` moved to adequacy. Earlier rows used slightly different groups, so they are only roughly comparable. The PR #21 row moved 236 lines from the simulation column to the shared code (net, per row: generic infrastructure −21 for the observations, machines −49 for the list lookups, optimize −62 and enclose −1 for well-scopedness and closedness, concretize −13 and globalize −44 for list and table lemmas, delay −47 for the renaming lemmas, composition +1); the shared code grew from 805 to 1071 lines, and adequacy shrank by 7 because its `Scope` now reuses the shared well-scopedness; before it, the interpreter column imported those lemmas from the simulation modules and was undercounted (1099 lines with four passes done, against 1130 with all five and the composition).

**Adding a feature: arithmetic (PR #25).** Every language got one operator `prim p ⦅ L , M ⦆`, for p ∈ {sub, eq} on integers, which evaluates both operands left to right and goes wrong unless both are integers. `eq` returns `inl ⟨⟩` for true and `inr ⟨⟩` for false, so `case` serves as `if`. Every pass maps over it. The code shared by all three proofs grew by 34 lines (the languages 15, the passes 6, and `Language/Prim`, 13). The proofs grew as follows:

| component | denotational: graph model | CEK machine + simulation | clocked interpreter + value relations |
|---|---:|---:|---:|
| domain, operators, continuity | +31 | — | — |
| semantics of the languages | **+16** | +65 | +54 |
| enclose | **+3** | +16 | +13 |
| optimize | **+3** | +16 | +13 |
| concretize | **+8** | +13 | +10 |
| delay | +35 | +17 | **+11** |
| globalize | **+7** | +15 | +11 |
| composition | **0** | **0** | **0** |
| shared modules not used by all three proofs | **0** | +8 | +8 |
| **total** | **+103** | +150 | +120 |

* **Denotational.** One semantic operator, `primD p D E = { out (δ p n m) | const n ∈ D, const m ∈ E }`, with its monotonicity, consistency and continuity (+31), one clause per semantics, and a congruence case per pass (`primD-≃`). The exception is delay (+35). Its relations treat flat values (constants, ω, ⟨⟩) as first-order data that need no reflection, and the results `left ⟨⟩` and `right ⟨⟩` of `eq` are not flat. So `Flat` became `Data` (flat values under `left` and `right`) in both directions, and reflect recovers the operands' constants.
* **Simulation.** Each machine gets two frames (`primL`, `primR`), three transitions and the value of a result (13 lines per machine). Each simulation relates the two frames and gets three cases and the lemma `prim≈` (related operands give related results, through `obs≈`, 6 lines).
* **Interpreter.** Each interpreter gets one clause and the value of a result (about 11 lines). Each pass gets one `run≈` case and the same `prim≈`.
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

| component | denotational: graph model | CEK machine + simulation | clocked interpreter + value relations |
|---|---:|---:|---:|
| semantics of the languages | +117 | **0** | **0** |
| rco | **+237** | +449 | +298 |
| shared modules not used by all three proofs | **0** | +278 | +278 |
| **total** | **+354** | +727 | +576 |

The +117 is `Clos5IswimContinuous`, moved from adequacy; the +278 are `PipelineScope` and `ScopeRename`, the scoping of `compile`'s output, moved from adequacy's well-formedness and split from its RB half. Adequacy went from 2238 to 2172 lines: Clos5 −117, well-formedness 287 → 60, shared +278 (the split costs 51 lines: `CompileWF` now proves only that each definition refers to older ones, `glob-rb`, and pairs it with `compile-scoped`).

**Explicate control and consistent binders (PR #28).** The first of the three rows of PR #28, by row (old method):

| component | denotational: graph model | CEK machine + simulation | clocked interpreter + value relations |
|---|---:|---:|---:|
| generic infrastructure | +4 | **0** | **0** |
| domain, operators, continuity | +29 | — | — |
| semantics of the languages | +113 | +62 | **+36** |
| concretize | +3 | **0** | **0** |
| delay | **−16** | 0 | 0 |
| rco | +5 | **0** | **0** |
| explicate control | +634 | +152 | **+145** |
| **total** | +772 | +214 | **+181** |

* **Explicate control.** The CFG machine (50) and interpreter (32), and the factoring of the Imp machine (+12) and interpreter (+4) that they share; the denotational semantics of CFG with the factoring of simple expressions in `Semantics/Graph/Imp.agda` (+42); the three proofs (634, 152, 145).
* **Consistent binders** (denotational +96, adequacy +74): the rest of the denotational rows (+4, +29, +71 of the semantics, +3, −16, +5), and adequacy's ISWIM (+52) and Clos5 (+22).

The second row (−334) replaced the direct semantics of Imp by the continuation-passing one in the main rows: lift locals 186 → 274, explicate control 634 → 210, semantics +2; the direct semantics and its two proofs (then 38, 107 and 558 lines, with the common modules factored out) became an experiment. The third row is the change of method explained above.

## Remove complex operands

The pass (`Compiler/RCO.agda`, Clos5 → Clos5, shared) binds every complex operand of a construct to a fresh variable by a `let`, left to right, and leaves atoms (variables, literals, code pointers) in place, shifted under the new lets; the result is in monadic normal form (`Language/Mon.agda`). It adds no calls and `let` does not tick. The late code check in the Clos4 and Clos5 machines and interpreters (see [Caveats](#caveats)) was added for this pass: with the check right after the operator, `app ⦅ L , M , N ⦆` with a non-code L errors before M runs, while its rco, `let x = L in let y = M in …`, would run M first.

* **Reduction (278 lines):** see [Reduction semantics + simulation](#reduction-semantics--simulation).
* **Denotational (237 lines): an exact equation.** `rco-correct : ⟦ rco M ⟧[ T ] ρ ≃ ⟦ M ⟧[ T ] ρ` for nonempty ρ, and `rco-program-correct : ⟦ rco-program P ⟧ₚ ≃ ⟦ P ⟧ₚ` for **every** program, with no scoping precondition. The laws are that `let` is strict and otherwise substitutes the meaning of its right-hand side (`let-strict`, `let-β`, which uses the continuity of Clos5), and that every construct whose operands rco names is a strict congruence (`Strict`); one lemma for the let chain (`lift-≃`) then gives each construct in one line. Order of evaluation is invisible: an error and divergence both denote ∅, and an unbound variable denotes {ω}.
* **Simulation (449 lines).** A forward simulation of the Clos5 machine by itself, for programs in `Scoped`. The target environment has the values of the lets in front, so terms are related up to a renaming (`Ren`). The source frames of a construct are related to the target's remaining let chain by `Pend` (one constructor per operand: a complex operand runs in lock step under a let frame, an atom is evaluated by the source while the target waits, with a decreasing index, and at the end the target runs the construct on its atoms up to the same final frame, `retT`).
* **Interpreter (298 lines): clock for clock, with equality of results.** For `Scoped` programs, `eval ds ck ρ M ≡ eval (map rco ds) ck ρ (rco M)` for every clock (`run≈`): values contain no code, so they are equal, not just related. The key lemma is the let chain (`lets≈`): evaluating the chain evaluates the complex operands left to right and then the construct with the atoms bound to their values; renaming commutes with evaluation (`ren`).

**Why the operational proofs need `Scoped`.** An atom left in place is evaluated after the complex operands that follow it. An unbound variable errors when it is evaluated, so it would error later: ``pair (` 0) L`` with L a loop errors in the empty environment, while its rco, ``let x = L in pair (` 1) (` 0)``, diverges. In the denotational semantics both denote ∅, so the equation holds anyway. `Scoped` (main closed, each definition in its two parameters) rules this out; the compiler produces such programs (`compile-scoped`, 249 lines, counted in the operational totals because only their `compile-mon` theorems use it, plus the 29 of `Syntax/ScopeRename`, now infrastructure).

The sizes in this section are as of PR #26 (now 243, 449 and 298).

## Lift locals

The pass (`Compiler/LiftLocals.agda`, shared, 44 lines) takes a monadic Clos5 term to Imp (`Language/Imp.agda`, shared, 35 lines). Imp has no binders: each body declares a frame of slots, a variable names a slot, `let` becomes the assignment `x := e₁; e₂`, and `case` assigns the payload to a slot. The frame is threaded: an assignment is seen by everything that runs after it in the same frame, also after the expression that contains it. A call runs the callee in a fresh frame (free variables in slot 0, argument in slot 1) and leaves the caller's frame as it was; reading or assigning a slot beyond the frame errors. Slots are de Bruijn levels: the variable x at depth d is slot d ∸ (x + 1), and a `let` or `case` at depth d assigns slot d, so code at depth d assigns only slots that no variable in scope names. The frame has d₀ + height slots (height = deepest nesting of binders), and a variable out of scope becomes slot n, beyond the frame. No proof needs a precondition, and the semantics of Imp in each style is new. As of PR #27 (since then, the denotational proof is against a continuation-passing semantics of Imp, and what follows describes the direct one, now an experiment; see [Explicate control](#explicate-control)):

| component | denotational: graph model | CEK machine + simulation | clocked interpreter + value relations |
|---|---:|---:|---:|
| semantics of Imp | +76 | +96 | **+61** |
| lift locals | +186 | +218 | **+143** |
| **total** | +262 | +314 | **+204** |

* **Denotational (76 + 186).** A store σ : ℕ → 𝒫 Value gives each slot a set of values, and an expression means, for the store it enters with, a set of values and the store it leaves (then `Sem/Imp.agda`, now `proof/Semantics/Graph/ImpDirect.agda`). `x := e₁; e₂` is Clos5's strict let, `⋆ ⟨ Λ F , D₁ ⟩`, applied both to the value and to each slot of the store e₂ leaves (`letₛ`); `case` is `𝒞`, likewise pointwise (`caseₛ`). The slots of a let or case collect only the runs of its body that have a value (`r ↓ y`): a run that errors or diverges leaves no store. Reading or assigning beyond the frame gave `init`, as an out-of-scope variable does in Clos5 (since explicate control, assigning beyond the frame means ∅). The invariant is the operational one, stated pointwise: at depth d the store agrees with ρ, slot d ∸ (x + 1) ≃ ρ x for x < d (`Agree`), and ρ is `init` from d on (`Scope`). The proof (`lift-sem`) shows at once that the value of `lift n d M` is ≃ `⟦ M ⟧ ρ` and that the store it leaves still agrees with ρ when that value is nonempty (`Out`), given `Agree`, `Scope` and `d + height M ≤ n`. Because the conclusion is relative to ρ rather than to the store M started with, coming back from under a binder is `weak` (`Agree (suc d) σ (X • ρ) → Agree d σ ρ`, one line, since `suc d ∸ suc (suc x)` is `d ∸ suc x` by computation), the analogue of the operational `weak`. Each simple construct is one congruence line; let and case reuse rco's `strict-≃`, `⋆-≃`, `Λ-≃` and `𝒞-≃`, and their stores are `out-let` and `out-case`. The nonempty condition is inherent: a stuck case or a let whose right-hand side has no value empties every slot too. No continuity is needed.
* **Simulation (96 + 218).** The Imp machine (`Semantics/CEK/Imp.agda`) carries the frame in its states and evaluates each atom in its own step, through the same continuation frames as the Clos5 machine, plus `assignK`, `caseK` and `callK` (which restores the caller's frame). A frame is related to the environment as `Fr n ρ (ρ ʳ++ τ)`: the environment reversed, then the free slots, n in all, so going under a binder is definitional. Continuations are related by `Kont` (one case per Clos5 frame, plus `weak`, a continuation at depth d is one at depth d + 1, which is where "code at depth d assigns only slots ≥ d" lives, and `call` for `callK`). Every source step is matched by exactly one target step, followed by any `callK` pops (`plus-simulation`, no measure); about half of the 70 lines of `sim` are one-line wrong-value cases.
* **Interpreter (61 + 143).** The interpreter `eval : ℕ → Frame → Exp → Result (Val × Frame)` ticks only at calls, like Clos5's, so the proof is clock for clock (`sim`), with values related by `≡` (Imp reuses Clos5's values) and frames by the same `Fr n ρ` as the simulation proof.

Unlike rco, the denotational proof is not the smallest here: the store is the new ingredient, and in the graph model it is a second, pointwise output (`Out` and the store halves of `letₛ`/`caseₛ`), while the operational proofs relate whole frames (`ʳ++`). With the invariant stated relative to the environment, as theirs is, the denotational proof is between the two operational ones.

**An experiment: the invariant relative to the environment.** The first version (74 + 204 lines) stated the store conclusion relative to the input store: `Pres d σ r`, the slots below d of the store r leaves are those of σ, as two inclusions, the second only when the value is nonempty, with `pres-refl`, `pres-ext`, `pres-case`, `pres-let`, and `agree-pres` to carry `Agree` across a store that `Pres` relates to the agreeing one (34 lines), and an `Agree` record that read slots through the frame check (needing `read-≃`). The current version (76 + 186) states it relative to ρ, as the operational `Fr n ρ (ρ ʳ++ τ)` does: `Out d ρ r = nonempty (proj₁ r) → Agree d (proj₂ r) ρ`. Then `Pres`, `pres-ext` and `agree-pres` disappear (`weak` is one line), the atomic cases leave the agreement they were given, and `out-case`/`out-let` are one ≃ each instead of two inclusion records. One change to the semantics makes this work: without it, `Out` would need an unconditional ⊆ half besides the conditional ⊇ half (a run of the body with no value still contributes its slots to the let's store), which is `Pres` again; the semantics now gates each run's slots by its value having an element (`_↓_`, 2 lines), which is also the more faithful reading: a run that does not finish leaves no store. Making the store a list, so that agreement is shaped like `ρ ʳ++ τ` and going under a binder is definitional, did not pay off and was not kept: with the function store and de Bruijn levels, `weak` is already definitional, the remaining slot lemmas (`read-at`, `read-out`, `upd-at`, `upd-<`, `slot-<`, 19 lines) have list counterparts of about the same size in the operational proofs (`‼-ʳ++`, `look`, `upd-++`, `assign`), and the pointwise store outputs of `letₛ`/`caseₛ` need a store whose shape does not depend on the run (a function, or a vector indexed by n), not a list. A store output for `letₛ` that is not strict cannot remove the nonempty condition, since a stuck `case` empties the store as well.

## Explicate control

The pass (`Compiler/Explicate.agda`, shared, 37 lines) takes Imp to CFG (`Language/CFG.agda`, shared, 28 lines), a C-like language after Essentials of Compilation. Imp's expressions without control flow became `Simple` (`Language/Imp.agda`), shared by the two languages. A CFG body has a frame size, a list of blocks and a start. A block is a tail: assignments `x := s` of simple expressions, ending in `return s`, `goto l`, or `case a x l₁ l₂`, which assigns the payload of a to slot x and jumps to l₁ or l₂. Blocks are listed newest first, as Clos5's global definitions are, and a block jumps only to older blocks, so control flow within a body is acyclic: no semantics needs a fixed point over the blocks, and the clocked interpreter does not tick at a goto (it recurses on the list of older blocks). The pass is in continuation-passing style (Danvy): `explicate-assign e x k` translates `x := e` followed by the tail k; a nested assignment `y := e₁; e₂` becomes `y := e₁` followed by `x := e₂` followed by k, and a case gets a join block that holds k, which its branches reach by `goto`, so k is not duplicated. `explicate-tail` translates an expression in tail position. The pass threads the list of blocks, only adding to it, so a tail refers only to blocks made before it.

| component | denotational: graph model | CEK machine + simulation | clocked interpreter + value relations |
|---|---:|---:|---:|
| semantics of CFG | 37 | 50 | **32** |
| explicate control | 210 (106 + 104) | 152 | **145** |

The CFG machine and interpreter reuse the evaluation of simple expressions factored out of the Imp machine (+12 lines there) and interpreter (+4); the denotational CFG semantics reuses `Semantics/Graph/Imp.agda`. No proof needs a precondition.

* **Simulation (50 + 152): a forward simulation with a measure** (`ExplicateSim`). The two machines share the frame and the evaluation of simple expressions and run in lock step except for the control flow that the pass makes explicit. An Imp expression runs as the tail that explicate makes of it in the mode of its continuation: `explicate-tail` in tail position, `explicate-assign e x k` when its value is assigned to x before k runs. So the stack of Imp continuations `x := □; e₂` is a CFG tail (`Ctl`: the tail made of e₂, or a `goto` to the join point that runs it). Imp's step into an assignment `x := e₁; e₂` has no CFG step: e₁ already runs as the tail the assignment runs as. This stutter is measured by the nesting of assignments (`depth`). A value returned to `x := □; e₂` is matched by the assignment and the chain of gotos to join points (`join`), a case by its jump to a block (`Br`). A tail made at the blocks bs runs with any newer blocks (`block-≼`).
* **Interpreter (32 + 145): clock for clock, with equal results** (`ExplicateFuel`). The pass keeps every call and gotos do not tick, so the interpreters tick in lock step; values are Clos5's in both, and code k names definition k of either program, so results are equal. `Means bs t K`: t, run with any blocks cs ⊒ bs, returns K applied to the frame. The CPS lemma (`assign-ok`): if k means K, `explicate-assign e x k` means running e, assigning its value to x and then K; `explicate-tail e` means the value of e (`tail-ok`); jumps to the join point run k with the blocks it was made with (`jump-at`).
* **Denotational (37 + 210): a congruence** (`ExplicateCommon`, `ExplicateCorrectK`), `explicate-correct : ⟦ explicate P ⟧ₚ ≃ ⟦ P ⟧ᴷₚ` for every program. A CFG tail, given the meanings of the blocks it can see and a store, means a set of values; the blocks of a body get their meanings newest first, as global definitions do, each with the meanings of the older ones, so no fixed point is needed (`Semantics/Graph/CFG.agda`). Against the continuation-passing semantics of Imp, the tail that `explicate-assign e x k` makes means e run with the continuation that assigns x and runs k, `⟪ explicate-assign e x k ⟫ ≃ ⟦ e ⟧ᴷ (assignK x ⟪ k ⟫)`, and `explicate-tail e` means e run with `halt`. Each case is a congruence: a nested assignment is e₁ with the continuation that assigns y and runs e₂ on both sides, and a case passes the continuation to its branches, which in CFG reach it through the join block. The common module (106) has what the proofs against both Imp semantics share: a tail made at bs means the same with newer blocks (`≼`, `blocks-at`, `goto-≃`, `Stable`), atoms and simple expressions, and the end-to-end theorems `compile-cfg-correct-const` and `-nonempty`.

**The counterexample, and consistent binders.** Explicate control is a commuting conversion: it moves the continuation of an assignment into the branches of a case. With the graph model as it was, where Λ and 𝒞 bind any finite set, the equation ⟦explicate P⟧ ≃ ⟦P⟧ was false, and a machine-checked counterexample showed it (`ExplicateCounterExample`, since removed). Take the Clos5 code `λ fv. λ Y. let y = case Y of inl _ ⇒ ⟨1,1⟩ | inr _ ⇒ ⟨2,2⟩ in ⟨fst y, snd y⟩`, lifted into Imp. The inconsistent argument Y = {left ν, right ν} makes the let bind y to a mix of the two branches, so ⟨1,2⟩ is a result in Imp but not in CFG, where each branch reaches the join point on its own. Such junk entries, elements that no run of a program produces, did not break the equations of the earlier passes; the commuting conversion is where they broke one. The fix was to the domain, not to the pass: Λ and 𝒞 now bind only consistent finite sets, so a denotation under a consistent environment has no inconsistent elements (see [Caveats](#caveats); +96 denotational lines, +74 adequacy, with delay 16 shorter). Separately, assigning beyond the frame in the denotational Imp and CFG now means ∅, as the machines error, instead of `init`, a value after which the program still ran: Imp checks the slot before the right-hand side runs and CFG after, and with `init` the pass could not preserve meanings.

**Two semantics of Imp.** Both are kept. In the direct semantics (`proof/Semantics/Graph/ImpDirect.agda`, from lift locals), an expression means a set of values and an output store. In the continuation-passing one (`Semantics/Graph/ImpK.agda`), `⟦ e ⟧ σ κ` runs e in the store σ and gives its value and the store it leaves to the continuation κ, the meaning of the rest of the body; the store is never collected over the runs of an expression. `Semantics/Graph/Imp.agda` (58) has what both share. With the direct semantics the commuting conversion is in explicate control: in Imp, `x := e; k` runs k in the store e leaves, collected over all runs of e, while in CFG k runs after each run on its own. Each step is a law (`let-assoc`, `let-case`); one direction is monotonicity, the other needs CFG tails to preserve directed unions of stores (`Dir`, `DC`) and the bound sets to be consistent, so that the finitely many runs k used can be merged into one (`merge`), and Imp to be monotone and consistent (`I-mono`, `I-con`). With the continuation-passing semantics, explicate control is the congruence above, and the commuting conversion moves into lift locals, against Clos5: the continuation commutes with let and with case (`let-law`, `case-law`, in `LiftLocalsCorrectK`), two small laws resting on the monotonicity and consistency of Clos5 (`Clos5IswimContinuous`). The chains, with the common modules counted in both denotational rows:

| | semantics of Imp | semantics of CFG | lift locals | explicate control | chain |
|---|---:|---:|---:|---:|---:|
| denotational, continuation-passing (main) | 84 (58 + 26) | 37 | 275 (105 + 170) | 210 (106 + 104) | 606 |
| denotational, direct (experiment) | 96 (58 + 38) | 37 | 213 (105 + 108) | 665 (106 + 559) | 1011 |
| simulation | 108 | 50 | 218 | 152 | 528 |
| interpreter | 65 | 32 | 143 | 145 | 385 |

The direct semantics makes lift locals smaller (213 against 275) and explicate control much larger (665 against 210): the store merging, directed continuity over stores, and the monotonicity and consistency of Imp are all in explicate control. With the continuation-passing semantics the denotational chain is 606 lines, against 528 (simulation) and 385 (interpreter); with the direct one it is 1011, about twice the simulation chain. The commuting conversion is where the graph model's junk entries broke the equation, and it is where the choice of the semantics of Imp matters most: done against Clos5's binders it costs two small laws, done against stores it costs the bulk of the direct proof.

## Select instructions

The pass (`Compiler/Select.agda`, shared, 39 lines) takes CFG to X86 (`Language/X86.agda`, shared, 49 lines): x86 with variables over **abstract values**, Clos5's, not over a heap. `alloc` and `load` build and take apart objects (tuples, pairs, sums, closures) with no addresses; a concrete heap would be a later pass (expose allocation). The locations are the slots of the frame and the registers `%rax`, `%rdi` and `%rsi`; there is one flag. The instructions are `movq`, `subq`, `cmpq`, `sete`, `testinl`, `alloc`, `load` and `callq`; a block ends in `retq`, `jmp` or `je`, and keeps CFG's label. A call passes the free variables in `%rdi` and the argument in `%rsi` and returns in `%rax`; each definition's prologue moves `%rdi` and `%rsi` to slots 0 and 1, and a call clobbers `%rdi`, `%rsi` and the flag. The callee starts with `%rdi` and `%rsi` as they are and with `%rax` and the flag unset; `callq` reads `%rdi` and `%rsi`, and `retq` reads `%rax`, so each errors on an unset register, in all three semantics (as of PR #33; before it, the machine and the interpreter passed the caller's `%rax` and flag to the callee and did not check the registers of a call or a return, which the X86 semantics, strict in them, does). Subtraction goes through `%rax` (two-address `subq`), `eq` is `cmpq; sete`, and `case` is `testinl`, a `load` of the payload and `je`. `compile-x86` is select ∘ `compile-cfg`. Main's frame has `locals` slots, as in CFG: with max(2, locals), as first specified, the end-to-end theorem would be false for open terms whose main reads slot 0 or 1.

| component | denotational: graph model | CEK machine + simulation | clocked interpreter + value relations |
|---|---:|---:|---:|
| semantics of X86 | 102 | 121 | **97** |
| select instructions | 322 | 272 | **140** |
| **total** | 424 | 393 | **237** |

* **Interpreter (97 + 140): clock for clock, with equal results** (`SelectFuel`), no precondition. Only `callq` ticks, and jumps recurse on the list of older blocks, as in the CFG interpreter. The interpreter runs a block's instructions in continuation-passing style, so the instructions select emits for a CFG statement unfold definitionally to that statement's step.
* **Simulation (121 + 272): a forward simulation** (`SelectSim`), no precondition. The X86 machine takes one instruction per step. The simulation runs from synchronisation points, each with a script (`Fate`) of how the two machines reach the next one: both stop (`stop`), the CFG steps while X86 waits (`lag`, measured by the length of the rest of the script), or the CFG steps and X86 takes one or more steps (`go`). Most of the cost is the timing of errors: each X86 instruction must error at the same CFG step that checks the same thing, and the operands of a call are read in a different order (X86 reads f last).
* **Denotational (102 + 322)** (`Semantics/Graph/X86.agda`, `SelectCorrect`): a continuation-passing semantics, as for Imp. Slot writes are strict, as CFG's `seq`; registers and the flag are written under a nonemptiness guard, so a failing or diverging instruction stops everything after it. (A first version let a register hold a failed value that a later write could forget; the guard cost +6 lines of semantics and +41 of proof. A guard rather than binding with ⋆⟨Λ…⟩ avoids a consistency lemma for the whole semantics.) `select-correct` needs every global definition to have at least 2 locals, because the denotational CFG semantics reads slots with bound `locals` while the X86 prologue writes slots 0 and 1; compiled programs satisfy it, so the `compile-x86` theorems have no extra precondition. The main costs are `case`, which needs the invariant that no slot holds both an `inl` and an `inr` (from the consistent binders), and about 85 lines of monotonicity of CFG tails in the store for the prologue's strict moves (`Mono`, `frame-≃`).

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

Code that other languages and compilers would use unchanged is reported in its own table and is not in any total. It is what a textbook or a verified compiler sets up once, before any particular language: Schmidt's semantic algebras and Winskel's metalanguage of domain constructions play this role for denotational semantics, and CompCert's general-purpose libraries and its generic transition systems and simulation diagrams (`Smallstep.v`) for the simulation style. The test is applied evenly to the four styles: would another language or compiler reuse the module as it is?

* **Infrastructure:** the abt library and the lemmas about the syntax of any signature (`Syntax/`: renaming, scoping, uses), list lookups (`ListUtil`), base types and `_⇔_` (`Primitives`, `Iff`); the denotational framework (sets as predicates, environments, the semantics of any signature and its monotonicity and consistency, `RenameSem`); the graph model, `GraphModel/` (formerly `Compiler/Model/Graph/Domain/ISWIM/`: values and consistency, the operators with their monotonicity, consistency and continuity, continuity of a semantics in its environment, formerly `Sem/Continuous`); the small-step framework (`Smallstep`, `Simulation`) and the clocked one (`Clocked`), both now parameterized over the type of observations (and, for `Clocked`, the observation of an error); since PR #37, substitution for any signature and its σ-calculus lemmas (`Syntax/Subst`, `Syntax/ScopeSubst`), the closure of a relation on terms under renaming and substitution (`Syntax/SubstRel`), and the reduction framework (`Reduction`: reductions as step functions with congruence rules, frames, answers, and the end theorem), which only the reduction column uses.
* **Not infrastructure:** the meaning of this compiler's primitives (`Semantics/Graph/Prim.agda`: `out`, `primD` and its lemmas), which stays in the denotational semantics row, as `prim?` stays in each machine and interpreter; this compiler's observations (`Semantics/Observation.agda`) and the instances of the operational frameworks at them (`Semantics/CEK/Smallstep.agda`, `proof/Semantics/CEK/Simulation.agda`, `Semantics/Interp/Clock.agda`, `Semantics/Reduction/Smallstep.agda`). The operational values are not infrastructure either: each language's `Val` is its own small datatype, closures over that language's terms or code pointers into its tables, observed through this compiler's observations, so no other language would reuse it as it is.
* **What it changed in the totals:** the rows "generic infrastructure" and "domain, operators, continuity" are gone, and so are the shared modules that became infrastructure; see [History](#history).

**Policy (since PR #42).** Language-independent reasoning is moved into the infrastructure on a best-effort basis, in all four styles alike. Language independent means reusable, unchanged, by other languages and compilers. The domain building blocks of the denotational semantics, such as products, sums and functions (pairs, tuples, injections and Λ with their operators and lemmas), are generic and count as infrastructure: they are the domain constructions of any language with those features. The operational values are not: each language's `Val` is tied to that language's syntax (closures over its terms, code pointers into its tables), and so is anything that names this compiler's `obs`, `prim?` or `Val`; they stay counted. That the denotational domains are independent of the syntax of the language, while operational value forms are not, is an advantage of the denotational approach, and the totals reflect it. The infrastructure sizes are always reported, per style, in the tables above, so the comparison can also be read with them included.

The script checks that no infrastructure module imports a module that is not infrastructure.

| language-independent infrastructure | lines | used by denotational: graph model | used by CEK machine + simulation | used by clocked interpreter + value relations |
|---|---:|---:|---:|---:|
| abstract binding trees | 220 | 220 | 220 | 220 |
| syntax lemmas (renaming, scoping, uses), list lookups | 273 | 212 | 273 | 273 |
| base types, logical equivalence | 26 | 22 | 26 | 26 |
| denotational framework | 395 | 395 | — | — |
| graph model: values, operators, continuity | 512 | 512 | — | — |
| small-step framework: transition systems, simulations | 187 | — | 187 | — |
| clocked big-step framework | 80 | — | — | 80 |
| **total** | 1693 | 1361 | 706 | 599 |

(As of PR #28; see [Current counts](#current-counts) for the current table.) The denotational proof relies on twice as much infrastructure as the simulation one: the graph model and the denotational framework (907 lines) against the small-step framework (187). As of PR #37 the reduction proof relies on 952 lines of it, 319 of them its own (substitution 189, the reduction framework 130). Adequacy uses 1519 lines of it, 158 of them (`Smallstep`, `Iff`, `Syntax.Scope`, `Syntax.ScopeRename`) not used by the denotational proof.

## The interpreter proof

Each interpreter is `eval : ℕ → Env → AST → Result Val`, where `Result Val` is `timeout`, `error` or `ret v`. It is defined by recursion on the clock and the term. The clock goes down only at a function call, and a call with clock 0 times out. The interpreter errors exactly where its machine stops with an error, and it evaluates in the same order: left to right, with the operator checked to be a function before the argument is evaluated (in Clos4 and Clos5: at the call, after all three operands).

Except simplify, no pass adds or removes function calls. Enclose, optimize, concretize and globalize map each application to one application. Delay maps it to a `let` around one application, and `let` does not tick. So every pass but simplify is proved **clock for clock**: for every clock, the program and its compilation both time out, both error, or both return related values. A generic lemma (`clocked`, 17 lines) turns this into both directions of the end theorem. There is no determinism argument and no simulation diagram. Simplify removes calls, and is proved clock-monotone instead (`clocked-le`; see [Simplify](#simplify)). The end theorem `compile-correct` in `CompilerFuel` composes the six results with `equiv-trans`, for the same `compile` and the same precondition (a closed ISWIM program) as `CompilerSim`.

The value relations and environment agreements are the same as in the simulation proofs. The saving is in everything the machines add: the continuation relation, one case per frame, and the states where one machine is ahead of the other. Pass by pass (interpreter against simulation):

* **enclose (162 against 222).** The difference is the continuation relation and the per-frame cases: a step of a frame becomes a `>>=` and `bind-rel`. Building a closure takes several Clos2 steps for one ISWIM step, which the machine proof matches by a plus; the interpreter just evaluates the captured variables.
* **optimize (194 against 273).** The source evaluates the free variables that the optimized closure drops, and the target does not. The machine proof needs a measure simulation: a match indexed by a natural number that each such stuttering step decreases, with states for the middle of dropping a variable. The interpreter has **no stuttering index**: a dropped free variable is a variable, which makes no call and, in a well-scoped program, cannot error, so the two interpreters call functions in lock step.
* **concretize (152 against 218).** A free variable becomes a projection from the tuple, three Clos3 steps for one Clos2 step, and building a closure takes one extra step. The machine proof relates a Clos2 state to a Clos3 state that is ahead of it (`Reach`, `enter`). The interpreter proof has **no run-ahead states**: a projection ``get i ⦅ ` 1 ⦆`` and the tuple of free variables are each evaluated in one go, with no intermediate state to relate.
* **delay (116 against 168).** An application becomes `let x = L' in app (fst x) (snd x) (shift M')`. The machine proof needs the run-ahead state `retT` and the four administrative steps that reach it. The interpreter proof has **no run-ahead state**: the `let`, `fst` and `snd` compute away, and `let` does not tick.
* **globalize (134 against 189).** Both proofs use the same **table-indexed relation**: the Clos5 program runs with the table D that the pass made for the whole program, the relation is indexed by D, and code `fun N` is related to `code k` when the table made by globalizing N is part of D. The lemmas about growing tables are shared. The difference is again the continuation relation and the frames.
* **composition (37 against 32).** Agda cannot infer the intermediate programs through the interpreters' `sem`, so the interpreter composition names them.

As of PR #26 (rco), the clocked interpreters (364 lines) are smaller than the machines (471): no continuations and no states. The generic part (80 lines against 188, now infrastructure: `Clocked` 80, `Smallstep` and `Simulation` 187) has no transition systems, simulations or determinism lemmas. In all, the interpreter proof was 1980 lines against 2653, both counting the 443 lines of shared syntactic lemmas and observations that only the two operational proofs use (165 before rco).

## Why delay costs more on the denotational side

As of PR #24, before arithmetic; the denotational proof of delay was 824 lines and the simulation one 151 (now 859 and 168, see [History](#history)).

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

**Simulation** (`proof/Correctness/CEK/DelaySim.agda`):

| part | lines |
|---|---:|
| relations: values, terms, environments, continuations; the run-ahead state | 58 |
| the simulation, all cases | 66 |
| end theorem | 7 |
| imports | 20 |

Its renaming lemmas, generic over any syntax (43 lines), are now language-independent infrastructure (`Syntax/Rename.agda`) and not counted.

**Where the ≈ 5.5× comes from:**

1. **Two directions instead of one: about 479 lines.** Delay changes how functions are represented, so the result is not an equation, and preserve and reflect need different relations. In the simulation proof, the backward direction comes from forward simulation plus determinism. The generic framework proves that once, and it is counted there. Preserve alone plus the shared part is about 345 lines, roughly 2.3× `DelaySim`.
2. **Finite observations in reflect: about 195 lines, plus part of the app case.** Pairs are joined (one value ⦅ u , v ⦆), but a target call still takes its code from `car C` and its free variables from `cdr C` separately, possibly from different pairs. A single target value says nothing about a call, so the relation ranges over finite lists, with batches and a depth index.
3. **β needs side conditions: about 130 lines.** In the graph model, β for closures, `let` and `case` holds only with nonemptiness and continuity. That costs `clos-β` and `cont-0` on both sides, the application equation, and consistency for `case`. Operationally, β is a machine step.
4. **Imports: 82 lines against 20.**
5. **Per-construct cases are comparable once the plumbing is gone.** Preserve's fundamental lemma is 78 lines against 66 for the simulation cases.

The cost is not in the compositional, per-construct reasoning. It is in the backward direction forced by the change of representation (item 1), and in the side conditions β needs in the graph model (item 3). The simulation proof pays for the backward direction once, through determinism. The denotational proof pays for it in each pass that is not an equation, and delay is the only such pass.

## Reduction semantics + simulation

The fourth column replaces the CEK machines of the languages with binders (ISWIM, Clos2–Clos5) by reduction semantics by substitution, and keeps everything else of the simulation style: the same observations, the same end theorem (`Equivalent`), forward simulations, and backward simulation from determinism. So the comparison with the CEK column isolates the choice of semantics.

**The semantics.** A state is a term. `red : AST → Red AST` says whether a term is a value, is stuck, or reduces, and a program's machine runs it (`Framework/Reduction.agda`). It is written with congruence rules: `step-in f (red X) k` reduces the subterm X in the context f, is stuck if X is, and continues with k if X is a value; so `red (app L M) = step-in (app □ M) (red L) (app? L (red M) M)`. This was chosen over evaluation contexts as the more compact: one function per language, with no decomposition into a context and a redex, no plugging, and no unique-decomposition lemma, deterministic and total by construction as the machines are; lifting a run of a subterm through a context is one generic lemma (`star-in`, `plus-in`) for any frame, a function g with `red (g X) ≡ step-in g (red X) (κ X)`. β, case and let substitute values (`Framework/Syntax/Subst.agda`, generic for any signature; cleared code, ∁, is not entered). Order of evaluation and the checks are those of the machines: the operator of an application is checked to be a function before the argument in ISWIM, Clos2 and Clos3, and only at the call in Clos4 and Clos5. A variable is never looked up: one that is reached is unbound, and errors. The reduction semantics (291 lines) are smaller than the machines (390), but need a predicate for their values and its two lemmas (120).

Imp, CFG and X86 have no binders: a reduction semantics for them would be a configuration-stepping machine on frames and blocks, which is what their CEK machines are. So the reduction column keeps those machines, and the proofs of explicate control and select instructions between them are the CEK column's, shared: they are counted in full in both columns (the semantics row includes the 267 lines of the three machines, and the two rows are the CEK proofs), so the sharing is no advantage to either.

**The simulations.** A relation on terms is a simulation when the reduction of every source term is answered by every related target term (`Ans`, `proof/Framework/Reduction.agda`): a value by a run to a related value, a stuck term by a run to a stuck term, a step by one or more steps to a related term. Congruence (`ans-in`) answers a construct from the answer of its operand, and the end theorem (`red-equivalent`) gives `Equivalent`. The target may have to take administrative steps before it stops (a projection in concretize, a let in delay, the evaluation of atoms in lift locals), so the small-step framework now also answers a stop by a run to a final state (`runs`; see [Caveats](#caveats)).

Pass by pass (reduction against CEK):

| pass | reduction | CEK | relation on terms | closed under substitution? | code of a closure related by |
|---|---:|---:|---|---|---|
| enclose | 221 | **193** | congruence + function/closure | yes | the compiled body under a substitution σ of the function's free variables |
| optimize | 248 | **245** | congruence + closure with `Pr` | yes | the compilation function (`opt-body` with prune's renaming) |
| concretize | **167** | 191 | congruence + closure + projection | yes | the compilation function (`conc-body`) |
| delay | 183 | **146** | congruence + closure/pair, app/let, call | yes | the relation itself (`M ≈ delay M`) |
| globalize | 201 | **168** | congruence + code/reference, table-indexed | yes | the compilation function (`glob`), through the table |
| rco | **278** | 410 | let chains, for every value | no | the compilation function under a substitution of values |
| lift locals | 323 | **186** | term in a context of lets ↔ Imp state | no | (frames, as in the CEK proof) |
| explicate control | **127** | **127** | shared with the CEK proof | — | — |
| select instructions | **238** | **238** | shared with the CEK proof | — | — |

* **The closure-conversion passes** (enclose to globalize) each need an inductive relation on terms, closed under substitution (`≈-subst`), which none of the other styles has: after a β the source is `N[V/x]`, and terms in general are no longer the compilation of anything. Closure under substitution is proved once per relation for any relation between substitutions that relates variables and is preserved under binders, and gives renaming and then substitution (`proof/Framework/Syntax/SubstRel.agda`, infrastructure); per pass it is one line per constructor (21 to 42 lines).
* **But the code of a closure is still related by the compilation function.** In Clos2–Clos5 the code of a closure is cleared (∁): no substitution enters it, so the target's code is the pass applied to the source's, as in the CEK proofs. Applying related closures substitutes related values into that code, which a fundamental lemma relates, `sub τ M ≈ sub τ' (pass M)` for related τ and τ' (enclose 37 lines, optimize 42, concretize 43): this is the substitution counterpart of the CEK proofs' environment relations. Only enclose's source code, ISWIM's λ bodies, is substituted into, and there the relation carries the substitution explicitly: `lam (N[σ]) ≈ clos (enclose N) F₁…Fₙ` when σ is related to what the closure captures. Delay and globalize do not look at variables, so for them the relation on code is the relation itself (`M ≈ delay M`, `M ≈ glob M`) and no fundamental lemma is needed.
* **Values are terms**, so the relation on terms is also the relation on values; there is no separate value relation, and no logical relation.
* **What substitution costs, and saves.** Enclose (+28), delay (+37) and globalize (+33) cost more than the CEK proofs: the relation on terms and its closure under substitution replace the relations on environments and continuations, and the congruence cases are about as many as the CEK proofs' frames. Enclose also tracks that the target stays closed, so that a closure whose captured variables were substituted is a value. Optimize is even: the reduction has no stuttering (a dropped free variable is a value after substitution, and takes no step, where the CEK machine evaluates it), but needs `Pr` for the closure's free variables and the closedness of the source. Concretize is smaller (−24): its run-ahead states (a variable becomes three Clos3 steps) become one clause, a value is related to a projection from the tuple of free variables, which takes one step. Concretize needs a new precondition, a well-scoped program (see [Caveats](#caveats)).
* **rco needs no closure under substitution** (−132 against the CEK proof). Its values are equal on both sides (they contain no code), so a complex operand M in the context h of its construct is related to its let in the target, `h[M] ≈ let x = M' in B`, when M ≈ M' and `h[V] ≈ B[x := V]` for every value V. The quantification is over a term, the same on both sides, so the relation is strictly positive and not a logical relation, and the simulation recurses into it. Every substitution is that of a β, a case or a let into code, related by `rco≈` (sub σ M ≈ sub σ (rco M) for σ mapping to values), which builds the let chains of rco by recursion on the operands (`chain`, 101 lines with the left-to-right frames of the constructs). The CEK proof needs renamings of environments and the pending chains (`Pend`) instead.
* **Lift locals costs most** (+137): it is the boundary between substitution and frames. The source is a term in a context of lets, the target an Imp state with a frame and a continuation, so the relation pairs the source's context with the target's continuation (`Kont`, as in the CEK proof), and values are related as data (term values with machine values). The source takes no step to evaluate an atom, which is already a value, while the target takes two, so each construct matches one source step with the target's evaluation of all its operands, case by case (the operands bound or not, and the shape of the values).

**Reading this column against the others.**
* **"Reduction semantics" here is substitution-based structural operational semantics**, a step function with congruence rules, not Felleisen–Hieb evaluation contexts (see *The semantics* above). A version with evaluation contexts would add decomposition, plugging and unique decomposition; it was not built, so its cost is not measured.
* **Substitution is infrastructure, so it is outside the total**, by the same rule that keeps the graph model out of the denotational total. The substitution library (189 lines, with `ScopeSubst` and `SubstRel`) and the reduction framework (130) are used only by this column; they are its counterpart of the graph model and denotational framework (767 lines), and like them they would be reused unchanged by another language. Both are in the infrastructure table.
* **About a fifth of the total is the CEK column's code.** The machines of Imp, CFG and X86 (267 lines) and the proofs of explicate control and select instructions (127 + 238) are the same files in both columns, 632 of the 3011 lines. The comparison of the two semantics is in the rows from enclose to lift locals, and the semantics row's reduction part (411 lines against the machines' 390).
* **The per-pass theorems differ in one place:** concretize is stated for well-scoped programs (`WS 0 M`), which the CEK theorem does not require (see [Caveats](#caveats)). The end-to-end theorems are the same as the CEK ones.

**The prediction** of [Which relations each proof needs](#which-relations-each-proof-needs) was that with substitution the closure-conversion passes would need relations on terms closed under substitution rather than the compilation function, that rco would too, and that lift locals, explicate control and select instructions would be unaffected. It held for the closure-conversion passes, with a refinement: the relation must be closed under substitution, but on the code of closures, which substitution never enters, the compilation function is still the relation (through a fundamental lemma quantifying over substitutions). It did not hold for rco, which needs no closure under substitution because its values are equal, and is smaller than the CEK proof. Lift locals is affected after all, as the pass from substitution to frames; explicate control and select instructions are indeed unaffected, and shared.

## Simplify

As of PR #41 (inlining; the rest as of PR #40). A source optimizer, the first pass of `compile` (ISWIM --simplify--> ISWIM --enclose--> …), proved in all four styles. It was first built as a pilot in the graph model and the reduction semantics, outside `compile`; then the CEK and interpreter proofs were added and it joined `compile` and the totals.

**The pass** (`Compiler/Simplify.agda`, 131 lines; ISWIM → ISWIM) is a simplified version of Chez Scheme's cp0. One recursive pass carries what it knows of each variable (`Facts`): the term that replaces it, and what it is known to be, if anything (`Info`): a value, or a function `λ N`, kept as its body N before simplification together with the `Facts` where it was defined (`Known`, cp0's operand structure in miniature); on a term it returns the same. It does

1. constant folding: a primitive whose operands are known integers becomes its result (`eq` gives `inl ⟨⟩` or `inr ⟨⟩`, the term of the semantics' `out`);
2. case of a known injection: `case L of x. M | y. N`, with L known to be `inl V`, becomes M simplified with x ↦ V (likewise `inr`);
3. projection from a known tuple: `get i L`, with L known to be a tuple of values, becomes its component i, or stays and is known to be it;
4. β on a value: `app (lam N) M`, and `let x = M in N` (since PR #43), where M simplifies to a value V, becomes N simplified with x ↦ V; this gives copy propagation and the elimination of dead bindings;
5. inlining: `app L M`, where L is known to be a function `λ N`, becomes N simplified at the call, with its variable bound to M as in β (`simp-let`, the same function as for 4), when the result has at most `inline-size` (24) nodes. The body is simplified again from the source, under the `Facts` of its definition and what is known of M, so the operand's value folds into it (`(λ f. f 3) (λ x. x - 1)` becomes `(λ f. 2) (λ x. x - 1)`; with `twice = λ f. λ x. f (f x)`, `twice dec 5` becomes 3). Fuel (`inline-fuel`, 4) bounds how deeply calls are inlined inside inlined bodies, so the pass stays structurally recursive (on the fuel, then the term) and `--safe`.

*Size policy.* Only small values are duplicated: variables, literals, `⟨⟩`, and `inl`/`inr` of one of those. A small value substituted for a variable keeps what is known of it, so a copy of a known function is known too (copy propagation without knowledge loss, which matters for inlining: `(λ f. f 3) g` with g known). Any other value (a function, a tuple, a nested injection) keeps its binding, as `let x = V' in N'` (before PR #43, the redex `app (lam N') V'`), and the bound variable is known to be V', so that a projection from it, or a case on it, can still be folded (example: `(λ p. get 1 p) ⟨λ y. y, 3⟩` becomes `let p = ⟨λ y. y, 3⟩ in 3`). An operand that is not a value keeps its binding and its evaluation.

*Semantic constraints.* The pass drops only the evaluation of a term whose value is known (the known value of a term is reached by evaluating it, without effect), and duplicates only small values; otherwise it keeps the order of evaluation. The operator of `app (lam N) M` is a function, so ISWIM's check that the operator is a function before the argument is evaluated is kept. Folding needs both operands to be known integer literals. Inlining follows cp0 (Waddell and Dybvig, SAS 1997): the operator, known, is dropped (its evaluation has no effect), and the operand is never substituted into the body unless it is a value: it stays bound, as `let x = M' in N'` (before PR #43, `app (lam N') M'`, which enclose turned into the allocation of a closure and an indirect call), so it is evaluated once, before the body, as in the source, and it is kept even if N' does not use it (an error or divergence is its effect). So inlining needs no restriction on the operand, and keeps evaluation order and termination; the target makes fewer calls than the source.

**The proofs.** Each simplify row also counts the syntactic lemmas that all four proofs use (`proof/Compiler/SimplifyFacts.agda`, 107 lines: the values `SV`, which `value` and `small` recognize, substitution keeps them, and what simplify's tests on known values found). The operational compositions also need that simplify keeps programs closed, for enclose's precondition (`proof/Compiler/SimplifyScope.agda`, 122 lines, shared, in the CEK, interpreter and reduction totals and in adequacy).

| | graph model | CEK machine + simulation | clocked interpreter + value relations | reduction semantics + simulation |
|---|---:|---:|---:|---:|
| the proof | **266** | 470 | 609 | 580 |
| simplify row (with `SimplifyFacts`) | **373** | 577 | 716 | 687 |
| of which, for inlining (PR #41) | **+11** | +37 | +48 | +75 |
| precondition | none | closed program | closed program | closed program |
| relation | equation | value relation (closures by `simp` under `Facts`), states frame by frame | the same value relation | relation on terms closed under substitution, with a step and a let rule |
| direction | — | target simulated by the source, with stuttering | forward at the same clock, backward at a larger one | target simulated by the source |
| new infrastructure | — | `equiv-sym` (5) | `clocked-le` (54) | `equiv-sym` (5) |

* **Graph model** (`proof/Correctness/Graph/SimplifyCorrect.agda`): an equation, `⟦ M ⟧ ρ₀ ≃ ⟦ simplify M ⟧ ρ₀`, from a main lemma: if what `simp` knows of each variable is true of the source's environment ρ in the target's ρ' (the term that replaces x, and its known value, denote ρ x in ρ'), then what it says of M is true. The transformations rest on β for a value: `⟦ (λ x. N) M ⟧ ρ ≃ ⟦ N ⟧ (⟦ M ⟧ ρ • ρ)` when `⟦ M ⟧ ρ` is nonempty and consistent, and the same for `case` on a known injection. **β for a value was not a problem** under the consistent-set binders: Λ and 𝒞 bind only finite, nonempty, consistent sets, and an element of `⟦ N ⟧ (D • ρ)` needs only a finite part of D (continuity, `body-continuous`, which moved from adequacy to the semantics row), which is consistent when D is. D is consistent because consistent environments give consistent denotations (`ISWIM-con-env`, already there), and nonempty because a value denotes a nonempty set (`sv-ne`, 15 lines) and D is equal to the denotation of the value it simplified to. So the main lemma carries one more invariant than enclose's, that both environments are nonempty and consistent (`Wf`), and the semantics needed no change. β for a value and for `case` on a known injection are 40 lines. No precondition: an unbound variable denotes {ω} on both sides.
* **CEK machine + simulation** (`proof/Correctness/CEK/SimplifySim.agda`): code in a machine state is a subterm of the program, and simplify's output is not a subterm of its input, so, as for enclose, the code of a target closure is related by the compilation function: `clo (simp (under E) N) ρ' ≈ clo N ρ` when the `Facts` E are true of the two environments (`Ok`: the term that replaces each variable denotes, in ρ', a value related to the source's (`Strong`), and its known value describes it (`Den`, the same up to functions, which are not inspected, so that known values may be shifted under binders without renaming code)). The simulation goes from the target to the source, and `Equivalent` is symmetric. The source runs ahead where simplify reduced (`run-term`, `run-known`: if simp's term is a value, or the term has a known value, the source runs to a value it describes, 110 lines), and the target stutters where it does more than the source: evaluating a small value where the source looks up a variable, and evaluating the value of a let that simplify kept, where the source has already bound it. A match is indexed by the number of target steps to a state related to the current source state, so the stuttering costs no measure. The relation on values and the descriptions are about 160 lines, the simulation about 270. The interpreter proof has its own copy of the relation and descriptions (the two styles have different value types, and a shared copy would be counted in the graph-model and reduction columns too).
* **Clocked interpreter + value relations** (`proof/Correctness/Interp/SimplifyFuel.agda`): **not clock for clock**. The clock ticks at each call, and simplify removes calls (β of a small value), so the target needs no more clock than the source, which may need more, by as many ticks as the eliminated calls are executed (unboundedly many). The theorem has the shape of the others (`Equivalent` of the two interpreters), from `clocked-le` (new in `proof/Framework/Clocked.agda`, 54 lines): if at every clock the source's result, unless it times out, is the target's (`LeResult`), the target's results grow with the clock, and whenever the target does not time out the source does not either at some clock, the two are equivalent. Simplify's proof gives the first (forward at the same clock, `run≈`, about 120 lines), the third (backward, `back`, about 105 lines: a result of the target is matched by a source result that is the same at every clock from some clock on, `Stable`) and the interpreter's monotonicity in the clock (`mono`, 38 lines; the forward direction also needs it, as the source's call takes a tick that the target does not). The source's run-ahead lemmas are as in the CEK proof, with stable results (104 lines), and the value relation is the CEK proof's.
* **Reduction** (`proof/Correctness/Reduction/SimplifyRed.agda`): the target takes fewer steps than the source, since simplify did some of the source's reductions ahead of time, under binders. So the simulation goes **from the target to the source**: each target step is answered by one or more source steps (the source catches up with the reductions simplify did, then takes the same step), with the existing framework (`red-equivalent`), and `Equivalent` is symmetric (`equiv-sym`). No stuttering is needed: values are terms, so a duplicated small value takes no steps. The relation (target on the left) is a congruence closed under substitution (`SubstRel`, as for the closure-conversion passes) with two more rules: *step*, the source reduces first; and *let*, a let of a value that simplify kept bound and known, whose bodies are related only after β (`N'[V'] ≼ N[W]`). Since simplify reduces under binders, the source's catching up happens on open terms, where a variable stands for a value: a reduction `⟶` of open terms (14 rules; 16 since PR #43), closed under substitution, which in a closed term is a step of the reduction semantics (`closed-red`) and keeps it closed; 130 lines in all. The main lemma takes two substitutions, the source's τ and the target's υ (the let rule substitutes a different value on each side), and a known value of a term is reached by the source (`eval-sv`: a term related to a value steps to a related value). The proof also has the values of the ISWIM reduction (25 lines; only simplify needs them). Its simulation (105 lines) is the shape of the other reduction proofs.
* **Inlining** (PR #41). In every style a known function is described semantically, through the source environment where it was defined: in the graph model `⟦ λ N ⟧ γf` for an environment γf of which its `Facts` are true; in the CEK and interpreter proofs a source closure `clo N ρf` with the `Facts` true of ρf (`KDen`); in the reduction proof `λ N` closed by a substitution τf of which they are true, which the source reaches. So no proof relates target code to target code: the inlined body is `simp` of the source body N, which the existing main lemma covers, under the function's `Facts` instead of the call's. The β lemma of each proof is generalized from `(λ N) M` to a function given by such a description (`let-ok`; in the CEK proof `let-sim`, `let-term`, `let-known`; in the interpreter `run-let`, `let≈`, `back-let`), and β and inlining both use it: for inlining the source first runs the operator to the known function (`run-known`, `eval-sv`), then takes the same steps as for β. The descriptions recurse through `Known`, so shifting them under a binder (`desc-shift`, `ok-weak`) is structural recursion on `Info`, and the main lemmas recurse on the fuel and then the term, as `simp` does. Copy propagation keeping what is known of a value needs one more fact in the operational proofs: that the term's value and its known value are reached by the same source run (in the CEK proof `run-unique`, from determinism of the machine; in the interpreter `stable-unique`; in the reduction proof determinism of the open-term reduction, `det`, 37 lines, the bulk of that column's increase). The reduction proof also needed a congruence for the operator (`app₁`), since the source now reduces an operator that is not syntactically a λ. The forecast (graph model +80–120, operational +150–250 each) was far too high: β for a value at a known function is the existing β lemma, generalized, not a new one.
* **The precondition** of the three operational proofs is a closed program, as for enclose: an unbound variable makes the source error where the target may have dropped it (`(λ x. 5) y`).

**Reading the sizes.** The graph model is the smallest by far: the reductions simplify does under binders are equations between denotations, and β for a value is one lemma, with no notion of a step, of who catches up with whom, or of clocks. Each operational proof must replay those reductions as steps: on open terms (reduction), or as a run-ahead of the source machine or interpreter (CEK, interpreter), with stuttering in the CEK proof where the target does more. The interpreter proof is the largest, because the clock breaks the usual clock-for-clock argument: it needs two inductions over the interpreter (one per direction), stable results and monotonicity. This is the first pass whose target takes fewer steps (and calls) than its source, and the first optimization that reduces under binders; both favour the equational style.

**Forecasts and actual sizes.** Before the CEK and interpreter proofs were written, the forecast was 350–450 lines for the CEK proof (actual: 453, 433 after a trim) and 250–350 for the interpreter (actual: 584, 561 after a trim). The interpreter forecast missed that clock-monotone correctness needs both directions as separate inductions, and the monotonicity of the interpreter.

* *Inlining* (transformation 5), forecast: graph model +80–120 lines, operational proofs +150–250 each; actual: +11, +37 (CEK), +48 (interpreter), +75 (reduction), see above.

## Adding let to ISWIM, Clos2 and Clos3

As of PR #43. A data point for the cost of adding one language construct in each style. ISWIM, Clos2 and Clos3 got `let x = M in N` (`let-op`, signature `■ ∷ ν ■ ∷ []`, as in Clos4, Clos5 and monadic Clos5), call by value: M is evaluated, then N with x bound to its value.

**Why.** Simplify's inlining (PR #41) leaves the cp0-style residual `(λ x. N') M'` when the operand M' is not a value, and it kept a binding of a non-small value V' the same way. Without `let` in Clos2, enclose closure-converts that residual into the allocation of a closure and an indirect call, so inlining a call with a non-value operand traded one call for another call plus an allocation. Now simplify emits `let x = M' in N'` in both cases (`simp-let`, shared by β, inlining and the source `let`), and enclose, optimize, concretize and delay map `let` to `let`, so no closure is allocated (example: `inline-let-enclosed` in `proof/Compiler/Examples/SimplifyExample.agda`: `λ g. let f = λ x. x - 1 in f (g 3)` simplifies to `λ g. let f = λ x. x - 1 in let x = g 3 in x - 1`, which enclose turns into two closures, those of the source's functions, and two lets). A source `let` is simplified like β: substituted when the bound term simplifies to a small value, kept (and known) otherwise. All the inlining, fuel and size decisions of PR #41 are unchanged.

**The semantics.** In the graph model `let` is β, as in Clos4: `⟦ let x = M in N ⟧ ρ = Λ (λ X. ⟦ N ⟧ (X • ρ)) ⋆ ⟦ M ⟧ ρ`, so its binder binds only finite, nonempty, consistent sets, and monotonicity, consistency and continuity are those of `Λ` and `⋆`. Each machine gets a frame `letK`, an eval rule and a return rule; each interpreter one clause (no tick: a let is not a call); each reduction semantics one congruence and one β rule (`N [ V ]`). The values of the reduction semantics are unchanged (a let is not a value).

The growth, per row (code lines, from `loc.py`; the shared code of all four proofs, the languages and passes, grew by 11 lines, not counted):

| component | denotational: graph model | CEK machine + simulation | clocked interpreter + value relations | reduction semantics + simulation |
|---|---:|---:|---:|---:|
| semantics of the languages | +28 | +9 | **+3** | **+3** |
| simplify | **+5** | +16 | +17 | +51 |
| enclose | +6 | +5 | **+3** | +8 |
| optimize | +5 | +6 | **+3** | +8 |
| concretize | +2 | +4 | **+1** | +5 |
| delay | +48 | +5 | **+1** | +6 |
| shared modules not used by all four proofs (scoping) | — | **+13** | **+13** | **+13** |
| **total** | +94 | +58 | **+41** | +94 |

Adequacy grew by 25 lines (ISWIM +12, the shared scoping lemmas +13), to 3233. The direct backward simulation for delay (an experiment) grew by 2.

* **Graph model.** The semantics row is the expensive one (+28: the clause in three languages, its monotonicity and consistency, and the continuity of ISWIM and Clos3), since each language needs its instance of every property. The passes that map `let` to `let` cost one congruence each (2–6 lines), by `⋆-≃` and the infrastructure's `Λ-≃` (PR #42), which compares bodies on the sets `Λ` binds; enclose and optimize lift their renaming of the environment under a binder to the top level, shared by `case` and `let`. Simplify cost 5 lines (3 of them the `let` cases of the syntactic lemmas in `SimplifyFacts`, in every column): in the graph model the emitted `let` means the same as the residual it replaces, and a source `let` means the same as a β-redex, so the β lemma is the one for `let`. **Delay is the exception (+48).** Its two directions are not equations: preserve needs β for a target `let` (by continuity; about 14 lines with its case), and reflect, over finite lists of target observations, must first gather the finite parts of the operand that the target's results use into one list (`let-collect`), then use β for a source `let` (about 34 lines). This is the same cost as for application in that proof (see [Why delay costs more on the denotational side](#why-delay-costs-more-on-the-denotational-side)), at a smaller scale.
* **CEK machine + simulation.** Enclose, optimize, concretize and delay cost one continuation constructor of the relation and two simulation cases each (4–6 lines), copied from `case`. Simplify (+16): the β lemmas were hard-wired to the source frame `appR (clo N ρf)`; they now take any frame that binds the body (`Binds`: a call or a `letK`), so β, inlining and the source `let` share them, and the target relation has one `letK` constructor. The emitted `let` is cheaper to simulate than the residual: the target no longer stutters through the `lam` and the operator frame.
* **Clocked interpreter + value relations.** The cheapest column (+41): one `run≈` case for each of enclose, optimize, concretize and delay (1–3 lines). Simplify (+17): the target `let` does not tick the clock where the old residual call did, while a source β or inlined call still ticks, so the lemmas shared by β, inlining and the source `let` became parametric in whether the source reaches the body by a call or by a let, with one helper per direction to absorb the tick.
* **Reduction semantics + simulation.** The congruence passes cost 5–8 lines each (one constructor of the relation, its substitution case, its fundamental-lemma case, and a simulation case copied from `case`). **Simplify is the most expensive here (+51).** Simplify reduces under binders, so the source's catching up is on open terms: the open-term reduction got two rules (`let` β and congruence) and their cases in determinism, substitution, closedness and scoping; and the relation's let rules doubled, since the target always has a `let` where the source has a `let` or a β-redex (congruence and kept value, against each source form). One lemma, parameterized by the source form, serves β, inlining and the source `let`.

**What made a style cheap or expensive.** Adding a construct that only the passes carry over unchanged costs each style one congruence case per pass, a few lines everywhere. The cost is elsewhere: in the graph model, in the per-language properties of the semantics (monotonicity, consistency, continuity) and in delay, whose relations are not equations, so every binding construct needs β with its side conditions and finite observations; in the operational styles, in simplify, where the source and target shapes differ (a `let` against a β-redex), which the CEK machine absorbs by abstracting over a frame, the interpreter by abstracting over a tick, and the reduction semantics only by doubling its rules and extending its open-term reduction. The scoping lemmas the operational compositions need (+13) are paid by each of them.

## Which relations each proof needs

As of PR #37 (PR #33 for the first three columns). For each pass, this records the relations each style defines between source and target: on values, on terms, or on whole states.

| pass | denotational: graph model | CEK machine + simulation | clocked interpreter + value relations | reduction semantics + simulation |
|---|---|---|---|---|
| enclose | equation | value relation | value relation | **term relation closed under substitution**; code: the compiled body under a substitution |
| optimize | equation | value relation | value relation | **term relation closed under substitution**; code: compilation function |
| concretize | equation | value relation | value relation | **term relation closed under substitution**; code: compilation function |
| delay | **logical relations** (both directions) | value relation | value relation | **term relation closed under substitution**; code: the relation itself |
| globalize | equation | value relation (table-indexed) | value relation (table-indexed) | **term relation closed under substitution** (table-indexed); code: compilation function |
| rco | equation | equal values | equal values | equal values; let chains related for every value; code: compilation function under a substitution |
| lift locals | equation | equal values | equal values | value relation (term values and machine values); terms in context and machine states |
| explicate | equation | equal values | equal values | equal values (shared with the CEK proof) |
| select | equation | equal values | equal values | equal values (shared with the CEK proof) |
| simplify (PR #40) | equation (β for a value) | value relation, with environments related through simp's Facts (Ok); target simulated by the source, with stuttering | the same value relation; clock-monotone, not clock for clock | **term relation closed under substitution**, with source steps on open terms and a let rule; target simulated by the source |

**Denotational.**
* Every pass but delay is proved as an equation, `⟦ pass M ⟧ ≃ ⟦ M ⟧`, which gives both directions at once. The proofs go by induction on the term.
* The only invariants are pointwise ones on environments or stores, for example:
  * enclose: environments agree on the variables the term uses;
  * optimize: environments agree through the renaming;
  * lift locals: the store agrees with the environment slot by slot;
  * select: no slot holds both an `inl` and an `inr`.
* Delay is the exception because it changes the representation of functions in the domain: a closure becomes a pair of code and environment. The two denotations are then not equal sets, so delay needs two relations:
  * forward, `v ⊑ D'`, by structural recursion on the source value;
  * backward, indexed by finite lists of target values and encoded with fuel.

  Domain values contain functions, so a function entry is related by quantifying over related arguments. These are true logical relations.

**Simulation.**
* Every pass needs a state relation, since a forward simulation is stated through one.
* Five passes also need a relation on values: the closure-conversion passes. Machine values contain syntax, a closure being code plus an environment, and those passes rewrite that syntax.
* The four Essentials of Compilation passes compute identical values. Their relations are about environments, frames, continuations and step timing.
* None of the value relations is a logical relation. Each is an inductive type defined by structural recursion on first-order values. A closure is related by naming its code (`enclose N`, `delay N`, a table entry) and relating its captured values, with no quantification over arguments. That is why the simulation delay proof is cheap.

**Interpreter.**
* The same five passes define a value relation `_≈_`, nearly identical to the simulation one; for globalize it matches constructor for constructor. The other four use equality.
* None are logical relations, for the same reason as in the simulation proofs.

**Reduction.** See [Reduction semantics + simulation](#reduction-semantics--simulation). The term relation is also the value relation, values being terms; none of its relations is a logical relation (rco's let chains quantify over a value term, the same on both sides).

**Relations on terms.**
* No proof in the first three styles defines an inductive relation on terms; the reduction proofs of the closure-conversion passes do, closed under substitution.
* *Simulation.* Wherever a state holds code, the target code is the pass applied to the source subterm, sometimes up to a renaming:
  * enclose's `eval~` relates `S.eval M ρ₁ κ₁` to `T.eval (enclose M) ρ₂ κ₂`;
  * globalize's `_↝_` only bundles "M' is `proj₁ (glob M ds)`, and the table grows into D".
* *Interpreter.* The theorems quantify over the source term and evaluate the compiled term directly. There are two near-exceptions:
  * the table relations `Def` (rco, lift locals) are the graph of the compiler on definitions;
  * explicate's `Means bs t K` relates a CFG tail to a semantic continuation, playing the role of the continuation semantics on the denotational side.
* *Denotational.* The compilation function is effectively the whole relation.

**The role of the CEK machines.**
* The machines never substitute into code. The code in a state is always a subterm of the program, or the body of a closure, which is also a subterm.
* So the code part of the relation can be "target code = pass (source code)", and everything dynamic sits in the relations on values, environments and continuations.

**With a reduction semantics (substitution) instead.** This was the prediction before the reduction column was built (PR #37); see [Reduction semantics + simulation](#reduction-semantics--simulation) for what it found. I expected the code part to stop being the compilation function for the closure-conversion passes:
* After a β-step the source term is `N[V/x]`. In general `pass(N[V/x]) ≠ pass(N)[V'/x]`, because optimize, concretize and enclose compute capture lists and layouts from free variables, which substitution changes.
* Intermediate terms also contain runtime values and administrative redexes that the pass never produced, such as rco's half-reduced let chains.
* Those passes would then need an inductive relation on terms, closed under substitution of related values, as in Plotkin's colon translation for CPS.
* Lift locals, explicate and select would be unaffected: Imp, CFG and X86 use frames and stores, not substitution.
* The denotational proofs would be unaffected too, since they never mention machine states.

**Summary.** The denotational side needs a value relation in one pass instead of five. But that one is a pair of logical relations, one of them over finite observations, and it costs most of the denotational delay proof (see [above](#why-delay-costs-more-on-the-denotational-side)).

## Experiment: a direct backward simulation for delay

The numbers in this section are as of PR #24, before arithmetic, which added 3 lines to `DelayBackSim` (149) and 17 to `DelaySim` (168); see [History](#history).

The simulation proof gets the backward direction of every pass from forward simulation plus determinism. A non-deterministic language cannot do that. This experiment measures what it would pay instead: the backward direction of delay, proved by a backward simulation that uses the determinism of neither machine. It is the simulation-style counterpart of the denotational reflect.

* `proof/Semantics/CEK/Backward.agda` (framework). A backward simulation, as in CompCert. The target moves, and the source answers each target step with a plus, or with a star that decreases a well-founded measure. A target stop with o is answered by a source star to a stop with o. Since the machines are total, no source-safety premise is needed. The end theorems are:
  * `backward-terminates : Terminates L₂ o → Terminates L₁ o`, for every o including o-error;
  * `backward-diverges : Diverges∞ L₂ → Diverges∞ L₁`, where `Diverges∞` is an infinite run. Without determinism, "runs of every length" (`Diverges`) does not give an infinite run, so the hypothesis must be one. The measure makes the simulation productive: along an infinite target run, the source cannot wait forever.
* `proof/Correctness/CEK/DelayBackSim.agda` (delay). The end theorems are `delay-back-terminates` and `delay-back-diverges`, for every Clos3 program. It reuses DelaySim's relations on values, environments and continuations (58 lines), and the shared renaming lemmas. The new part is the state relation. Where the target takes administrative steps for one source step, the source waits and the index counts the target steps left:
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

* A direct backward proof in the simulation style of delay is about as big as the forward one: 146 lines on top of the shared relations, or about 204 standalone, against 151. The cases are as easy as the forward cases (one line each, by computation of the step function). The extra lines list the administrative target states, 12 constructors of the state relation and one `waits` line per state.
* It stays well under the denotational reflect (453 lines in its two modules, 479 with the depth bound it uses). So the simulation advantage on delay is not only "backward comes free from determinism". Even without determinism, a step-indexed backward simulation needs no finite-observation machinery. A target run is a finite sequence of steps, each answered locally, while a denotational element of a target application summarizes many calls at once.
* Generically, the direct backward framework (94) is somewhat larger than the determinism argument (71). And a non-deterministic language would need it alongside a forward simulation in every pass that changes representation, here about 150 lines more for delay. The determinism argument is paid once.

## Graph model with errors

As of PR #53. The **graph model with errors** is a denotational semantics in which an error and divergence differ: a program that stops with an error denotes a set that holds ω, one that diverges denotes ∅. Since PR #51 it is defined for every language of the compiler, every pass is proved correct in it, and it is adequate for the ISWIM, Clos5 and X86 machines on all three outcomes. It is the fifth column of [Current counts](#current-counts), counted as the four are but not (yet) in their comparison; its adequacy is reported separately. PR #50 was the pilot (ISWIM to Clos4, through delay). Since PR #53 its operators are built from an error monad on 𝒫 Value, with the graph model's operators as kernels; the counts before the monad are kept in [Before the monad](#before-the-monad).

**Why.** Every operational semantics here is a total function, so every error is *trapped* (Cardelli): the program stops with `o-error`. The operational theorems (`Equivalent`) tell the three outcomes of a run apart: an answer, an error, divergence. The graph model does not: an error and divergence both denote ∅, so the denotational end-to-end theorem plus adequacy can only say "the same constants, and an answer exactly when the other has one" (`Theorems/Adequacy.agda`). The graph model with errors closes that gap.

**The payoff** (`Theorems/GraphErrors.agda`). For a closed ISWIM program M, the ISWIM machine on M and the Clos5 machine on `compile M`, and likewise the X86 machine on `compile-x86 M`:
* stop with an error together (`end-to-end-error`, `end-to-end-x86-error`);
* stop with the same constants (`end-to-end-const`, …);
* stop with an answer together (`end-to-end-converges`, …);
* diverge together (`end-to-end-diverges`, …).

This is `Equivalent` for errors, constants and divergence. An answer that is not a constant (a function, a tuple, an injection) is observed only as an answer, as in the graph model, since delay and the later passes change how closures are represented. Underneath:
* every pass but delay is an equation (≃);
* delay preserves and reflects an error, the constants and having a value;
* so each compiled program (Clos5, monadic Clos5, Imp, CFG, X86) is `Same` as the source: ω together, the same constants, a value together (`compile-*-correct`);
* adequacy for each of the three machines characterizes all three outcomes.

**The design** (`Framework/GraphModel/ErrorMonad.agda`, `Semantics/GraphErr/`; since PR #53 an error monad, see [Before the monad](#before-the-monad)):

1. **An error denotes ω.** The error is the existing `ω` of the domain (`Framework/GraphModel/Domain.agda`). There is no second error value.
   * `ω ~ ω` is its only consistency.
   * Every `ρ₀` already maps an unbound variable to `{ω}`, as a free variable is an error in the machines.
   * A program that stops with an error denotes a set that holds ω; one that diverges, ∅.
2. **An error monad on 𝒫 Value.** A set D is a computation: it errs when ω ∈ D, its values are `⌊ D ⌋` (its elements other than ω), and it diverges when it has neither.
   * `D ≫= F` holds ω when D does, and `F ⌊ D ⌋` when D has a value. `binds n` binds n operands, left to right: an operand that diverges before one that errs gives no error, and a continuation never sees ω.
   * `checked k X A` is A, and ω when X has a value whose `kind` is not k (a function, a pair, an injection, a tuple of n components, a base type).
   * Proved once: the monad laws, monotonicity, consistency and continuity of bind and the check, and that bind preserves a lifted relation.
3. **Each operator is a graph-model operator under binds**, in its machine's order: its kernel is the graph model's operator (`Framework/GraphModel/Ops.agda`), and a kernel that inspects its operand's kind adds `checked`.
   * **Early check.** ISWIM, Clos2 and Clos3 check the operator first, as their machines do: `⋆ᵐ D E = D ≫= λ F → checked fun F (E ≫= λ X → ⋆ F X)`. Applying a non-function errs even when the argument diverges.
   * **Late check.** Clos4, Clos5, Imp, CFG and X86 bind code, environment and argument and only then check the code: `callᵐ = binds 3 (checked fun F (⋆₂ F E X))`.
   * Tuples, pairs, closures' free variables and a primitive's two operands are `binds`; projections, `fst`, `snd`, case, `payload` and `isinl` bind their operand and check its kind; X86's strict writes are `D ≫= λ _ → E`; a slot written beyond the frame is `D ≫= λ _ → {ω}`.
   * Each operator's `Good` record (monotone, consistent, continuous) is derived from its kernel's, in one line.
4. **Binders bind no ω** (`Λᵐ = Λ ⇂ ValEntry`, and 𝒞's payloads). Operands never are ω (the bind sees to that); the filter keeps the passes equations: with plain Λ, ISWIM's `λx. λy. x` has the entry `[ω] ↦ ν`, where its Clos2 closure has `[ω] ↦ ω`.
5. **The first-order languages err where their machines do** (PR #51): a missing definition is `errcode`, code whose call errs; a slot read beyond the frame is `{ω}`, and a write errs once its value is computed; an unset register or the absent flag holds `{ω}`; an `alloc` of the wrong arity and a jump to a missing block err.
6. **The monad, the operators and their laws are infrastructure** ("graph model with errors: the error monad, its operators and laws", 935 lines): the laws the passes and adequacy use (left unit on a set of values, a let is the bind of its body, a case and a check commute with a bind, the β laws of code and calls, congruences by monotonicity) are stated once over the operators. Only the primitives (`primᵐ`), the tables, the frame check and language-specific lemmas are counted.

**Counts** (from `loc.py`; code lines; the four columns of [Current counts](#current-counts)):

| | graph model with errors | before the monad | graph model | CEK machine + simulation | clocked interpreter + value relations | reduction semantics + simulation |
|---|---:|---:|---:|---:|---:|---:|
| semantics of the languages | 447 | 639 | **443** | 660 | 466 | 644 |
| simplify | 349 | 380 | **343** | 572 | 644 | 710 |
| CC: enclose | 90 | 109 | **81** | 188 | 140 | 186 |
| CC: optimize | 149 | 186 | **134** | 224 | 170 | 222 |
| CC: concretize | 134 | 151 | 141 | 182 | **127** | 157 |
| CC: delay | 898 | 1037 | 594 | 134 | **90** | 183 |
| CC: globalize | 157 | 157 | 155 | 157 | **111** | 192 |
| rco | 194 | 206 | **118** | 396 | 245 | 247 |
| lift locals | 138 | 129 | 142 | 172 | **98** | 306 |
| explicate control | 144 | 145 | 154 | 124 | **118** | 124 |
| select instructions | 363 | 349 | 271 | 235 | **107** | 235 |
| composition | 33 | 33 | 32 | 26 | **22** | 27 |
| shared modules not used by all four proofs | **398** | 398 | — | 456 | 456 | 456 |
| the graph model's meaning of the primitives | 34 | 34 | — | — | — | — |
| **total** | 3528 | 3953 | **2608** | 3526 | 2794 | 3689 |

How to read the table:
* **Semantics** (447 against 639). Each language's semantics is a table of operators. Before the monad the row also had Clos2's continuity (`Clos2Continuous`, 135 lines), which no proof used; it is gone.
* **Shared modules.** Like the operational proofs, the errors model needs closedness and the scoping of `compile`'s output, because a free variable errs (`EncloseScope`, `SimplifyScope`, `PipelineScope`).
* **The pass rows**:
  * **Optimize** (149). A closure binds its free variables; dropping one that is a set of values is the left unit (`≫=-val-β`), and a kept one is bound on both sides (`≫=-≃`). The theorem is for well-scoped programs (`WS 0`, which enclose produces).
  * **Delay** (898, +51% over the graph model): backward relation 244, application equation 15, backward fundamental lemma 376, forward direction 263. Each construct is a bind lemma over its operands and its kernel. The cost over the graph model is in what is related (errors and kinds observed backward, values forward, the early and the late check), not in the error bookkeeping.
  * **Rco** (194). Every operator rco names the operands of is `binds n` of a kernel (`Kernel`), and a let is the bind of its body (`letᵐ-≫=`), so binding an operand by a let is the operator's own first bind. Before the monad this took a list-of-operands lemma per operator (`ErrorStrict`, 136 lines of infrastructure).
  * **Lift locals** (138 against 129). Its continuation is a bind into a finitary continuation (`K⟨_⟩`, `KOK`), which commutes with a let by associativity and with a case by `𝒞ᵐ-≫=`; finitary-ness is carried through the proof (from `body-continuous`), which is the 9 lines more.
  * **Select instructions** (363 against 349). A strict write changes nothing when the value it writes binds the same atoms (`strictᵐ-skip`); X86's case (test, bind the payload, branch on the flag) is `case-core`, element by element as before.
* **Adequacy**:

| adequacy | graph model with errors | before the monad | graph model |
|---|---:|---:|---:|
| ISWIM | 790 | 915 | **663** |
| Clos5 | 904 | 1153 | **712** |
| X86 | 2096 | 2149 | **1115** |
| well-formedness of compiled programs | 364 | 364 | **262** |
| end to end | 39 | 39 | **25** |
| simplify through the ISWIM machine | 30 | 30 | — |
| shared modules not used by all four proofs, nor by the proof of its model | **58** | 58 | 456 |
| the graph model's adequacy modules it uses | 52 | 52 | — |
| **total** | 4333 | 4760 | **3233** |

  * Each logical relation has one bind lemma that handles an operand's error (`ℂ-bind`, `𝕄-bind`), and one lemma for a failed kind check, through `kind` (`𝒱-bad`, `𝕄-check`); the per-operator error cases are gone.
  * **X86** (2096). Soundness (1260) still has one case per way the machine stops with an error (`final-err`); the logical relation (589) is where the monad saves. The consistency of the tables (`X86Consistent`, 110) is the operators' consistency.

**Infrastructure** reached by each graph model: see the table under [Language-independent infrastructure](#language-independent-infrastructure) above (the `both` column). The errors model now shares the graph model's operators (474 of their 623 lines: `Ops` and its proof half, `Continuity`, `DomainUtil`) as kernels, and adds 935 lines of its own (the monad, its operators and laws), against 1317 before. `loc.py` checks that it reaches no module of the other proofs except the graph model's meaning of the primitives and these operators, and prints the operator modules it reuses.

**What is still hard.**
* **Evaluation order.** Which operand errs first decides the result; the monad states it once (nesting of binds), but the relations of delay and adequacy still relate each error.
* **The early and the late operator check** are two operators, as in the machines.
* **Closed and well-scoped programs.** Simplify and enclose hold for closed programs, optimize and rco for well-scoped ones, because a free variable errs.
* **Inference.** Agda cannot infer a bind's continuation from an element of the bind (`≫=` unfolds under ∈), so each use of a bind lemma names it.

## Before the monad

PRs #50 and #51 built the graph model with errors with its own error-propagating operators (`ErrorOps`, `ErrorContinuity`, `ErrorStrict`, `ErrorLaws`: 1317 lines of infrastructure, none of the graph model's operators reused). Its counts: semantics and passes 3953 (delay 1037), adequacy 4760, infrastructure reached 2670. PR #53 rebuilt it on an error monad, first as a pilot beside it (ISWIM to Clos4, simplify, enclose, concretize, delay, ISWIM adequacy) and then for the whole column, which replaced it: passes and semantics 3528 (−11%), adequacy 4333 (−9%), error-specific infrastructure 935 (−29%), with the graph model's operators shared. The table above gives the old count of each row.

## Typed intermediate languages (pilot)

Not in the totals. Today ISWIM and every intermediate language are untyped. Each semantics checks the kinds of values itself, and a misuse stops with the trapped error `o-error` / ω. The pilot asks whether that error handling goes away when casts are inserted early, as in *Essentials of Compilation*, ch. 9, so that the intermediate languages are statically typed. It covers ISWIM → Clos4 in two contrasting columns, the CEK machines and the graph model with errors. Its statements are in `agda/Theorems/Typed.agda`.

    ISWIM --cast insertion--> ISWIMᵀ --enclose--> Clos2ᵀ --concretize--> Clos3ᵀ --delay--> Clos4ᵀ

There is no optimize: enclose's output goes to concretize directly.

**Design.**
* **Types** (`Language/Typed/Type.agda`).
  * `Any` is a value of any flat type, tagged with that type.
  * The flat types mirror the untyped values: `base B`, `tup n` (n values of type `Any`), `sum` (inl or inr of an `Any`) and `fun` (`Any → Any`).
  * `code n` exists in Clos4ᵀ only: closed code that takes an environment of type `⟪ tup n ⟫` and an argument.
  * Decidable equality of flat types is needed by `project`. For base types it is new infrastructure (`Framework/PrimitivesDec.agda`).
* **Intrinsic syntax** (`Language/Typed/{ISWIM,Clos2,Clos3,Clos4}.agda`).
  * Terms are indexed by a context and a type, so a misuse or a free variable cannot be written.
  * In ISWIMᵀ and Clos2ᵀ every variable has type `Any`, and a context is a number. In Clos3ᵀ and Clos4ᵀ it is a list of types.
  * `project G` is the only operation that can fail.
* **Cast insertion** (`Compiler/Typed/Cast.agda`, 26 lines), on well-scoped programs (`WS 0`, that is, closed ones).
  * A value is injected with its flat type.
  * Each operation projects its operand where the ISWIM machine checks it:
    * `(L M) ⇒ app (project fun L') M'`, the operator before the argument;
    * `get i L ⇒ get i (project (tup n) L')`;
    * `case L … ⇒ case (project sum L') …`.
  * A primitive checks its operands only after it has evaluated both, so they are let-bound first: `prim p L M ⇒ let x = L' in let y = M' in inject (prim p (project Int x) (project Int y))`. The pass carries a renaming for that let.
* **Typed closures.**
  * Enclose captures every variable of the context, so a closure's body is unchanged. The untyped pass captures the shortest prefix that covers the body; pruning is optimize's job.
  * In Clos2ᵀ and Clos3ᵀ a closure is a value of type `⟪ fun ⟫`, and its value hides the length of its environment.
  * In Clos4ᵀ, `⟪ fun ⟫` is the existential `∃ n. code n × ⟪ tup n ⟫` of typed closure conversion (Minamide, Morrisett and Harper). The witness is a natural number, since every environment is a tuple of `Any`.
    * `pack` builds a closure.
    * `unpack L B` opens one. Its body `B : (n : ℕ) → Tm (⟪ tup n ⟫ ∷ code n ∷ Γ) Any` is a family of terms, one for each length. That constructor branches infinitely but is strictly positive, so Agda's `--safe` accepts it.
    * Opening a closure needs no check. There is no unchecked or untyped access to the environment, and no trapped check that cannot fail.
  * Delay is `app L M ⇒ unpack L' (λ n → call (` 1) (` 0) M')`, with a renaming for the two variables.
* **CEK machines** (`Semantics/CEK/Typed/`). Values, environments and continuations are typed, and a state is well typed by construction. Each machine has one way to stop with `o-error`, a failed project. The untyped machines have five or six, plus an unbound variable.
* **Graph model with errors** (`Semantics/GraphErr/Typed/`).
  * The operators are the graph model's under the binds of the error monad, with no `checked`.
  * `inject` is the identity, since a value's kind is its tag.
  * `project k D = D ≫= λ X → checked k X (X ⇂ kind ≡ k)`. It keeps only the values of the right kind; without that filter a denotation is not consistent.
  * In Clos4ᵀ a function is a pair, so `project fun` checks for a pair.
  * `unpack` runs its body for the length n of the environment, read off the kind `tup n` of its values. Running it for every n would give `const n` for every n in a body that ignores its environment.

The pilot's proof agents found these last three points: their first versions were wrong.

**Counts** (from `loc.py`; code lines). The rows of "today" are those of the same segment in [Current counts](#current-counts). The languages, passes and semantics rows count only ISWIM–Clos4; the passes are shared by both columns. In each column the lower of today and typed is bold.

| typed pilot, ISWIM → Clos4 (not in the totals) | CEK machine + simulation: today | CEK machine + simulation: typed | graph model with errors: today | graph model with errors: typed |
|---|---:|---:|---:|---:|
| languages ISWIM–Clos4 (shared) | 115 | **101** | 115 | **101** |
| passes (shared): cast insertion | — | 26 | — | 26 |
| passes (shared): CC: enclose, concretize, delay | 89 | **79** | 89 | **79** |
| passes (shared): CC: optimize | 55 | — | 55 | — |
| passes (shared): the compiler | — | 3 | — | 3 |
| semantics of the languages | 324 | **322** | **215** | 368 |
| lemmas shared by the passes | — | 30 | — | — |
| cast insertion | — | 195 | — | 122 |
| CC: enclose | 188 | **106** | 90 | **38** |
| CC: optimize | 224 | — | 149 | — |
| CC: concretize | 182 | **115** | 134 | **69** |
| CC: delay | 134 | **101** | **898** | 919 |
| composition | — | 5 | — | 16 |
| **total, without optimize** | **1032** | 1083 | **1541** | 1741 |
| **total** | 1311 | **1083** | 1745 | **1741** |

| infrastructure group | lines | graph model | graph model with errors | both | adequacy adds: graph model | adequacy adds: graph model with errors |

* **The CC passes shrink in both columns**, except delay in the graph model with errors.
  * **CEK:**
    * enclose 188 → 106;
    * concretize 182 → 115;
    * delay 134 → 101.
  * **Graph model with errors:**
    * enclose 90 → 38;
    * concretize 134 → 69;
    * delay 898 → 919.
* **Cast insertion is new**, and it is where the kind errors are now handled: CEK 195 (147 for the simulation, plus 48 lines of list and primitive lemmas copied from adequacy so that the pilot does not import it), graph model with errors 122.
* **The segment as a whole is not smaller.**
  * CEK: 1083 against 1032 without optimize, or 1311 with it.
  * Graph model with errors: 1741 against 1541, or 1745 with optimize.
* **The typed CEK machines are no shorter** (322 against 324). The kind cases are gone, but typed continuations, the length equations of tuple frames (`Framework/VecUtil.agda`, infrastructure) and inject/project frames take their place.
* **The typed graph semantics (368) is 99 lines of definitions and 266 lines of lemmas.** The lemmas cover monotonicity, consistency and continuity, which the untyped semantics get from the generic fold over abstract binding trees (`GoodSemantics`, infrastructure).
  * The typed semantics are defined by recursion on intrinsically typed terms, so each language proves these itself: Clos2ᵀ 44, Clos3ᵀ 121, Clos4ᵀ 101 (the continuity of `unpack`, β of code).
  * Concretize and delay need them for the β laws of closures.
  * A generic fold for intrinsically typed syntax would move most of these lines into infrastructure.
* **The audit surface of the pilot:** 715 lines of its own (types, languages, passes, semantics, statements), against 115 lines of languages, 89 of passes and the semantics rows today.

**Error handling removed.**
* **CEK.**
  * The untyped enclose, concretize and delay spend 15, 15 and 11 clauses on a value of the wrong kind (`stops refl`). Untyped delay also needs a state for the early operator check (`retT`, `ret-reach`).
  * Untyped enclose carries the scoping bookkeeping of free variables (`Agree`, `Lookup` with `Maybe`, `bound`).
  * The typed proofs have none of these: the coverage checker rules the cases out.
  * What is left of errors is 6 lines per proof for project, a step that succeeds or stops in both machines, plus 7 shared lines (`Lock`).
  * Cast insertion spends about 28 of its 147 lines on errors.
* **Graph model with errors.**
  * Enclose and concretize handle errors with one congruence line each for `project`, plus 6 lines (`project-good`).
  * In cast insertion, about 81 of 122 lines relate a check to a project.
  * Delay is the exception (below).
* **The early and the late operator check** are gone. ISWIMᵀ to Clos3ᵀ application and Clos4ᵀ's call check nothing, because cast insertion has already put the operator's project where the ISWIM machine checks it. Typed CEK delay is a plain plus simulation.

**Why typed delay in the graph model is not smaller** (919 against 898; 594 in the graph model without errors). The types did remove the early and late checks, the let through Λ, and the checks of prim, get and case: the backward fundamental lemma went from 376 to 333. Three costs come back.
* **The relation cannot be indexed by types.** `Any` contains `⟪ fun ⟫`, so the types are recursive. The forward relation still recurses on source values. The backward relation is still indexed by the depth of finite target lists. A closure's calls still mix the code and environments of several pairs (`Calls`, `collect`).
* **Project's filter** relates sets restricted by kind on both sides (about 80 lines with its error).
* **Others:**
  * a typing invariant that a value of type `⟪ fun ⟫` is a function (25 lines);
  * the renamings of typed delay (about 35);
  * the semantic lemmas above.

  Giving a Clos4ᵀ closure the kind of a function, so that `kind₄ = kindᶠ`, would save an estimated 30–40 lines.

**Forecast for the rest of the pipeline, if continued typed.**
* **Globalize** (Clos4ᵀ → Clos5ᵀ). Code references index a typed table of definitions (`fun-ref : Σ ∋ n → Tm Γ (code n)`), so a call to a missing definition cannot be written. Growing tables (`GlobalizeTable`) become weakenings of the table's membership. Expect the CEK proof to shrink as enclose and concretize did (157 → about 100), and the graph proof to stay an equation (157 → about 80), plus about 100 lines of semantic lemmas for Clos5ᵀ.
* **Rco.** Its operands are let-bound at any type (`code n`, `⟪ tup n ⟫`), so typed `let` must be general in its type. There is no late check to preserve, and that check is what makes rco's untyped CEK proof (396) the largest pass proof after simplify. Expect a large CEK saving and a smaller one in the graph model with errors (194).
* **Lift locals and Imp.** A frame can be typed by a context: a slot is a typed index `Γ ∋ A`, and its size is fixed by the type. Reading or writing a slot beyond the frame, and the frame check, disappear. Each slot keeps one type, which lift locals already does: one slot per variable.
* **Explicate control and CFG.** Labels can be block indices (`Fin`), so a jump to a missing block and the case on a non-injection disappear. This is cheap: CFG's blocks are first order.
* **Select instructions and X86.** X86 stays untyped: registers and stack slots hold any value, and its machine keeps its trapped errors (an unset register, a missing label, a missing flag). Select must then show that compiled code never hits them, an invariant like adequacy's `X86WF`. That is the one place where errors would still be handled. With a typed CFG they are unreachable rather than propagated, so select is unlikely to shrink; it may grow.
* **Adequacy** (both graph columns).
  * The source is still untyped ISWIM, so ISWIM adequacy is unchanged.
  * Clos5 adequacy would be for Clos5ᵀ, whose logical relation needs no kind cases but cannot be indexed by the recursive type `Any`, as for delay.
  * X86 adequacy is unchanged.
  * Cast insertion's ≃ in the graph model with errors costs no new adequacy.

**Recommendation: no-go for turning the comparison typed; keep the pilot as an experiment.**
* Typing does what was hoped in the passes: kind and scoping errors disappear, and the early/late check issue is gone. The CC passes shrink by 25–60%.
* But cast insertion has to handle the kind errors once (195 / 122 lines), and the typed CEK machines are no shorter.
* In the graph model with errors, delay does not shrink, and the semantic lemmas that the generic fold provides for untyped syntax have to be redone for each typed language.
* So the segment is about 5% larger in the CEK column and about 13% larger in the graph model with errors (without optimize).
* The later passes would likely gain more (rco, lift locals, explicate control), and X86 would gain nothing.
* Two things could turn this around:
  * a generic semantics framework for intrinsically typed syntax (infrastructure), which would remove the 266 lines of semantic lemmas;
  * running the comparison from a typed source language, which would remove cast insertion.

