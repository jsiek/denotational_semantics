# Size of the compiler-correctness proofs

<!-- toc -->

- [[#Current counts]]
  - [[#Adequacy]]
  - [[#No-error lemmas]]
  - [[#Infrastructure]]
  - [[#Audit-surface counts]]
  - [[#Shared modules]]
  - [[#Scott domains]]
- [[#Dynamic typing and errors]]
- [[#Mixing semantics]]
- [[#The ISWIM pipeline in full]]
  - [[#Counts of the ISWIM pipeline]]
  - [[#Audit-surface counts (ISWIM)]]
  - [[#Shared modules (ISWIM)]]
  - [[#Infrastructure modules (ISWIM)]]
  - [[#Assurance]]
  - [[#Typed against untyped]]
  - [[#The untyped pipeline (preserved)]]
- [[#What the groups contain]]
- [[#Caveats]]
- [[#Audit surface]]
- [[#History]]
- [[#Remove complex operands]]
- [[#Lift locals]]
- [[#Explicate control]]
- [[#Select instructions]]
- [[#Adequacy for X86]]
- [[#Language-independent infrastructure]]
- [[#The interpreter proof]]
- [[#Why delay costs more on the denotational side]]
- [[#Reduction semantics + simulation]]
- [[#Simplify]]
- [[#Adding let to ISWIM, Clos2 and Clos3]]
- [[#Which relations each proof needs]]
- [[#Experiment: a direct backward simulation for delay]]
- [[#Graph model with errors]]
- [[#Before the monad]]
- [[#Typed assembly language]]
- [[#Typed intermediate languages (pilot, superseded)]]

<!-- /toc -->

All four proofs establish end-to-end correctness for the same compiler, ISWIMμ's `compile-x86` (`agda/Mu/Compiler/Pipeline.agda`), which runs

    ISWIMμ --simplify--> ISWIMμ --enclose--> Clos2μ --optimize--> Clos2μ --concretize--> Clos3μ
           --delay--> Clos4μ --globalize--> Clos5μ --rco--> Monμ --lift locals--> Impμ
           --explicate control--> CFGμ --select instructions--> X86μ

ISWIMμ (`agda/Mu/`, module prefix `Mu.`; the design is `notes/iswim-mu-design.md`) is ISWIM, intrinsically typed, with base types, functions, n-ary tuples, sums and iso-recursive types `μX.A` (any body: being iso-recursive, they need no contractiveness condition, since PR #86), whose `fold` and `unfold` do nothing at run time (the identity in the graph model, a wrapper and its elimination in the machines, interpreters and reduction semantics, a move in X86μ). It has no recursion construct and no error: Ω and the call-by-value fixed-point combinator are typable through μ (`Mu/proof/Compiler/Examples/`), and nothing traps. Every language of the compiler is intrinsically typed, down to the typed assembly language X86μ (`Mu/Language/X86.agda`), after Morrisett, Walker, Crary and Glew's TAL, as X86ᵀ is (see [[#Typed assembly language]]), without a check: a sum's `case` is one typed pseudo-instruction. Simplify (`Mu/Compiler/Simplify.agda`) is a source optimizer on ISWIMμ, a simplified cp0. The languages, passes and proofs are a parallel copy of those of the typed ISWIM pipeline (below), without cast insertion: `agda/Mu/X.agda` corresponds to `agda/X.agda`, with `Language/Typed/` as `Mu/Language/` and `Semantics/<style>/Typed/` as `Mu/Semantics/<style>/`. ISWIMμ reuses `agda/Framework/` unchanged; its own infrastructure is heterogeneous vectors (`Mu/Framework/`), since contexts, tuples and tables are lists of types. The prefixes of the compiler, `compile₄` (into Clos4μ), `compile` (Clos5μ), `compile-mon` (Monμ, run as its embedding into Clos5μ), `compile-imp` (Impμ) and `compile-cfg` (CFGμ), are each proved end to end too.

ISWIMμ is the main experiment. The ISWIM pipeline (`agda/`), whose source is untyped and whose compiler inserts casts, shows how dynamic typing and errors change the comparison: it is reported briefly in [[#Dynamic typing and errors]] and in full in [[#The ISWIM pipeline in full]] (`loc.py --iswim`), with a fifth column, the graph model with errors. The untyped pipeline that preceded it is preserved in `agda/Untyped/` (`loc.py --untyped`; see [[#The untyped pipeline (preserved)]]). The sections after [[#History]] were written for the untyped ISWIM pipeline, and their numbers are its own, as of their PRs; ISWIMμ's proofs follow the typed ISWIM pipeline's pass by pass, and a note *ISWIMμ* at the start of a section points to the current counterpart of what it describes.

* **Denotational: graph model** ("graph model" in short): a graph-model semantics for each language and one correctness proof per pass, in `agda/Mu/Semantics/Graph/` (the proofs under `agda/Mu/proof/Correctness/Graph/`, the lemmas about the semantics under `agda/Mu/proof/Semantics/Graph/`), over the graph model in `agda/Framework/GraphModel/`. The theorem (`Mu/Theorems/Denotational.agda`): every pass but delay preserves the meaning exactly (≃); delay preserves and reflects constants and nonemptiness; so the compiled program produces the same constants as the source, and produces something exactly when the source does.
* **CEK machine + simulation** ("simulation" in short; the style of CompCert): a small-step CEK machine for each language (for X86μ, a machine with a call stack, registers, the open closure and a flag; Monμ runs as its embedding on the Clos5μ machine) and one forward simulation per pass, in `agda/Mu/Semantics/CEK/` (the proofs under `agda/Mu/proof/Correctness/CEK/`). The theorem (`Mu/Theorems/Simulation.agda`, end to end `PipelineSim`): the two programs terminate with the same observation, and one diverges exactly when the other does.
* **Clocked interpreter + value relations** ("interpreter" in short; the style of CakeML): a functional big-step semantics with a clock for each language (a total interpreter that ticks the clock at each function call and times out when it runs out) and one clock-for-clock proof per pass (simplify, which removes calls, clock-monotone), relating the results of the two interpreters by a relation on values, in `agda/Mu/Semantics/Interp/` (the proofs under `agda/Mu/proof/Correctness/Interp/`). The theorem (`Mu/Theorems/Interpreter.agda`) has the same shape as the simulation one, over the same observations: a program terminates with o if it does so for some clock, and diverges if it times out for every clock.
* **Reduction semantics + simulation** ("reduction" in short; small-step reduction by substitution, as in PLT Redex, with CompCert-style simulations): a reduction semantics by substitution for each language with binders (ISWIMμ, Clos2μ–Clos5μ), a step function written with congruence rules, and one forward simulation per pass between terms, in `agda/Mu/Semantics/Reduction/` (the proofs under `agda/Mu/proof/Correctness/Reduction/`), over the reduction framework `agda/Framework/Reduction.agda` (infrastructure). Impμ, CFGμ and X86μ have no binders, so they keep the machines of the CEK column, and the proofs of explicate control and select instructions between those machines are shared with it (counted in both columns). The theorem (`Mu/Theorems/Reduction.agda`) has the same shape as the simulation one; see [[#Reduction semantics + simulation]].

**All four columns prove the same end-to-end theorem.** For a closed program `M : Tm [] (base Int)`, the source and the compiled X86μ program stop with the same constant, or both diverge:

| style | constants | divergence |
|---|---|---|
| graph model + adequacy | `Mu/Theorems/Adequacy.agda`: `end-to-end-x86-const` | `end-to-end-x86-diverges` |
| CEK machine + simulation | `Mu/Theorems/Simulation.agda`: `compile-x86-const` | `compile-x86-diverges` |
| clocked interpreter + value relations | `Mu/Theorems/Interpreter.agda`: `compile-x86-const` | `compile-x86-diverges` |
| reduction semantics + simulation | `Mu/Theorems/Reduction.agda`: `compile-x86-const` | `compile-x86-diverges` |

The operational columns derive both from their `Equivalent` (`compile-x86-correct`, which holds at every type). The graph model derives them from its own end-to-end theorem (`compile-x86-same`, stated in `Mu/Theorems/Denotational.agda` as `compile-x86-correct-const` and `-nonempty`, and for `main : Int` as `compile-x86-int-const` and `-nonempty`: the same constants, nonempty together), and adequacy for the clocked interpreters of ISWIMμ and X86μ (see [[#Adequacy]]), which relates constants and, through the emptiness of the denotations, divergence directly, with no no-error lemma. So the graph model states the interpreter column's theorem, about the same interpreters. So the caveat that the columns state different theorems does not apply to ISWIMμ, and it needs no graph model with errors.

Counts are code lines: lines that are neither blank, nor comments, nor part of an import statement (`import` or `open import`, with its continuation lines). Imports are left out because their number depends on how finely a development is split into modules, not on what it proves; they were counted until PR #35 (see [[#History]]). The tables are regenerated with
`python3 papers/PLDI-2027/loc.py` from the repository root, which prints ISWIMμ's tables and then the short comparison with the ISWIM pipeline (with `--iswim` for the ISWIM pipeline's full tables, `--untyped` for the untyped pipeline's, `--mu-detail` for ISWIMμ against the ISWIM pipeline row by row, `--mixed` for mixing the graph model and the interpreters, see [[#Mixing semantics]]; the table of contents and the links between sections are Obsidian heading links, regenerated and checked by `python3 papers/PLDI-2027/toc.py`). The script fails if any Agda module is not assigned to a group, if a proof of any pipeline imports another proof's modules, adequacy's, an example's or an experiment's (ISWIMμ's columns may use what the ISWIM pipelines share, such as the meaning of the primitives and the instances of the frameworks at this compiler's observations), if a module outside `agda/Untyped/` imports one inside it, if a module of the language-independent infrastructure imports anything that is not infrastructure, if a module of an audit surface imports a proof module (the theorem files excepted), or if a module outside the `proof/` directories is not used by a theorem statement: those of `agda/Mu/` by ISWIMμ's, in `agda/Mu/Theorems/` (see [[#Audit surface]]). A module split into definitions (`agda/Mu/X.agda`) and lemmas (`agda/Mu/proof/X.agda`; likewise `agda/X.agda` and `agda/proof/X.agda`, and `agda/Untyped/X.agda` and `agda/Untyped/proof/X.agda`) counts as one module, in one group. The import bundles `Framework.GraphModel.Prelude` and `Framework.GraphModel.ErrorPrelude` (and their `proof/` halves), which only re-export the modules that every semantics and proof in the graph models opens, are in no group: an import of a bundle is read as imports of the modules it re-exports, so the bundles change no count.

**How totals are computed.** Each module belongs to one group: a column of one of the pipelines, adequacy, shared, language-independent infrastructure, examples, or an experiment. A few groups belong to two columns: the machines of Clos5μ (whose values the Impμ machine uses), Impμ, CFGμ and X86μ and the proofs of explicate control and select instructions are shared by the CEK and reduction proofs, and are counted in full in the corresponding rows of both (likewise in the ISWIM pipeline). A proof's total is its own modules plus every shared module that it imports, directly or transitively, *unless all four proofs of its pipeline import it*, plus, for ISWIMμ, the ISWIM pipeline's modules it reuses (the graph model's meaning of the primitives; the instances of the small-step, reduction and clocked frameworks at this compiler's observations). So each column is the standalone size of that proof, apart from two things. What is common to all four proofs: the languages, the compiler passes and `compile-x86`, and the lemmas about the compiler's output that all four use. And the language-independent infrastructure, code that other languages and compilers would reuse unchanged (the abt library and syntax lemmas, typed indices and vectors, heterogeneous vectors, the denotational framework, the graph model and the semantics of intrinsically typed syntax in it, the small-step, reduction and clocked frameworks, and substitution; see [[#Language-independent infrastructure]]). Neither is counted in any column; the infrastructure has its own table, which shows what each proof relies on. A shared module that only some proofs use is counted in each of them, in the main ISWIMμ table in the semantics row, together with the ISWIM pipeline's modules the column reuses (elsewhere, the row "shared modules not used by all four proofs"); they are listed [[#Shared modules|below]]. Examples are not counted. Adequacy is reported separately (see below). The import graph is read from the `import` and `open import` lines.

## Current counts

*Other measures.* `loc.py --tokens` and `loc.py --chars` count the same code in lexical tokens and in non-whitespace characters. After the final cleanup pass (PRs #88–#91), the ISWIMμ totals are 38106, 45314, **31181** and 63923 tokens and 73680, 90244, **62838** and 123391 characters (graph model, CEK, interpreter, reduction), against 1806, 2103, **1504** and 3093 lines: the same ranking, with 20.7–21.5 tokens per line in every column. By tokens, explicate control goes to the interpreter (1500 against 1595); by characters, the semantics (13068 against 13193) and enclose (1334 against 1511) go to the graph model, and explicate control stays with it (3152 against 3475); the composition goes to reduction under all three measures; every other row has the same smallest column under each measure.

In every table that compares the proof styles, the lowest number of each row is in bold: the best result for that row. Tables of infrastructure are not marked, since relying on less of it is not in itself better.

The four styles on ISWIMμ (`loc.py`). Each semantics row counts the shared modules that the four do not all reach (the observations, 15, in the operational columns) and the ISWIM pipeline's modules the column reuses (the graph model's meaning of the primitives, 34; the instances of the small-step, reduction and clocked frameworks at this compiler's observations, 2–4). The closure-conversion passes (enclose, optimize, concretize, delay, globalize) are labelled "CC: " in the tables, since simplify, rco and the later passes are not part of closure conversion:

| component (ISWIMμ) | denotational: graph model | CEK machine + simulation | clocked interpreter + value relations | reduction semantics + simulation |
|---|---:|---:|---:|---:|
| semantics of the languages | 427 | 529 | **391** | 980 |
| lemmas shared by the passes | — | 38 | — | — |
| simplify | **349** | 560 | 508 | 697 |
| CC: enclose | 37 | 71 | **33** | 147 |
| CC: optimize | 66 | 128 | **65** | 212 |
| CC: concretize | 46 | 88 | **42** | 148 |
| CC: delay | 450 | 73 | **35** | 126 |
| CC: globalize | **115** | 213 | 175 | 192 |
| rco | 109 | 120 | **83** | 157 |
| lift locals | 39 | 51 | **27** | 204 |
| explicate control | **64** | 105 | 75 | 105 |
| select instructions | 76 | 107 | **48** | 107 |
| composition | 28 | 20 | 22 | **18** |
| **total** | 1806 | 2103 | **1504** | 3093 |

Not counted: ISWIMμ's languages and passes (921, shared by all four, with simplify and the renaming of ISWIMμ that it shares with the reduction semantics), the primitives and registers (13), and the infrastructure (below). The CEK and reduction columns share the machines of Clos5μ, Impμ, CFGμ and X86μ and the proofs of explicate control and select instructions (counted in both, `mu-op+mu-red`).

* **The ranking:** interpreter (1504) < graph model (1806) < CEK (2103) < reduction (3093), after the final cleanup pass of every column (PRs #87–#91; before it, 1653 < 1961 < 2258 < 3207), the same as the ISWIM pipeline's (1814 < 2131 < 2582 < 3620; see [[#Dynamic typing and errors]]).
* **Delay decides the graph model's place.** Without delay the graph model is 1356, below the interpreter (1469), CEK (2030) and reduction (2967); delay alone is a quarter of the graph column (450), against 73, 35 and 126. Delay is not a cost of errors (see [[#Dynamic typing and errors]]): it is the change of representation of closures under recursive types, which needs the approximant logical relation and its depth index (see [[#Why delay costs more on the denotational side]]).
* **Every other row of the graph model is near the interpreter's or below it.** The equational passes are cheap where the interpreter's value relations are cheap: simplify is 349 (graph), 560 (CEK), 508 (interpreter), 697 (reduction); the closure-conversion passes but delay (enclose, optimize, concretize) 149, 287, 140, 507; the back end (globalize to select) 403, 596, 408, 765. The graph model is lowest on simplify, globalize (115 against 175 for the interpreter, which relates the two tables of definitions value by value) and explicate control.
* **Simplify** (`Mu/Compiler/Simplify.agda`) is the ISWIM pipeline's simplify (a simplified cp0: constant folding, case of a known injection, projection from a known tuple, β on a value or a let, inlining with fuel, the same substitution policy and sizes), intrinsically typed, with one more known-value rule: `unfold` of a term known to be `fold V` becomes V (V if small, otherwise the unfold, known to be V), as a projection does. Its rows are 349, 560, 508 and 697 against the ISWIM pipeline's 342, 574, 640 and 716 (both with their syntactic lemmas, `SimplifyFacts`, in each column). Before the final cleanup pass they were 360, 584, 633 and 715: typing removes the scope invariant (`WS`, `Closed`), the error cases of the machines and interpreters, and the lengths of tuples, and the new rule, `fold`/`unfold` and the typed indices cost about as much. The cleanup, which the ISWIM pipeline's proofs did not get, made the operational rows smaller than the ISWIM pipeline's, the interpreter's most (633 → 508: one induction, `sim`, proves both directions at each clock, and one, `run`, lets the source run ahead for a term and for a known value; `let-sim` for a let), the CEK one's by one run lemma, `run`, with `let-run` and `call-run`, for a term and for a known value (584 → 560). The graph model pays 7 more: untyped ISWIM gets renaming and continuity from the syntax of any signature, ISWIMμ proves its renaming lemma in the simplify proof (`ren-≃`, 26) and its continuity by induction on the term (`Mu/proof/Semantics/Graph/ISWIM.agda`, 20, in the semantics row, shared with adequacy). See [[#Simplify]].
* **Semantics:** the graph model's and the interpreter's are the smallest (427 and 391, with the meaning of the primitives and the observations; the graph model's is a meaning function per language, no values, continuations or clocks, ISWIMμ's continuity, and the binder congruences that the pass proofs share, `Mu/proof/Semantics/Graph/Binders.agda`, 17), the reduction semantics' the largest (980: substitution's laws, and the machines of the first-order languages; ISWIMμ's renaming and substitution, 31, are shared with simplify and so not counted, while `loc.py --mu-detail` keeps them in ISWIM's row against ISWIMᵀ's).
* **Lemmas shared by the passes** (CEK only, 38): the Clos5μ machine on atoms (`Clos5Common`, 11, used by rco and lift locals), and the relation between the values of two machines for a pass that maps the code of each closure (`Mu/proof/Semantics/CEK/Rel.agda`, 27, with `obs≈` and `δ≈`, used by enclose, concretize and delay instead of three copies). Since PR #89 the machines of ISWIMμ and Clos2μ–Clos4μ share their values (`Mu/Semantics/CEK/Values.agda`, 25, in the semantics row), parameterized by the code of a closure, as the interpreters' do. The machines collect a tuple's values newest first in a heterogeneous vector (`_<><_`, `Mu/Framework/AllUtil.agda`), as the ISWIM pipeline's do in a vector since PR #67, so no proof needs the lengths of the tuples collected so far.
* **Select instructions** is CFGμ → X86μ, an equation (≃) in the graph model, a forward simulation in the CEK and reduction columns (the same proof), clock for clock with equal results in the interpreter. X86μ holds the values of Clos5μ in CFGμ's frame, so no proof relates values or frames; it has no check. See [[#Select instructions]] and [[#Typed assembly language]].
* **The composition** is one line per pass and the two statements for `main : Int` in the operational styles: reduction 18 (one chain to Clos5μ), CEK 20 and interpreter 22 (through Clos4μ; the interpreter's no longer has statements at Clos5μ); the graph model's composes ≃ and delay's `Same` (28: `then` composes two `Same`s, `same` lifts an equation).

### Adequacy

Adequacy relates the graph model of ISWIMμ and X86μ to their clocked interpreters, the semantics of the interpreter column. It turns `CompilerCorrect`, the end-to-end theorem for the whole compiler, `compile-x86`, into statements about running programs (`Mu/proof/Adequacy/EndToEnd.agda`; stated in `Mu/Theorems/Adequacy.agda`). It is reported separately, because the denotational semantics can be taken as *the* semantics of a language, in which case adequacy is not needed; its sizes are internal information, not part of the comparison. It is an add-on to the denotational proof, so its total also counts the shared modules it imports that the denotational total does not already count (the observations and `GlobalizeOlder`, that globalize refers only to older definitions); the denotational total plus the adequacy total is then standalone (3335, the graph model's proof to running code), except for the infrastructure and for the interpreters, which adequacy reuses from the interpreter proof and which are not counted again. Until 2026-10-15 (see [[#History]]), adequacy was for the CEK machines (1599 now, total 3405 to running code); that proof is kept as an alternative (`Mu/proof/Adequacy/CEK/`, side `mu-adeq-cek`, reachable from `Mu/All.agda` but not stated in `Mu/Theorems/`, in no total) and shown beside it. The tuples of sets (`Tuples`), the tables' lemmas (`Clos5Common`) and the well-formedness of compiled programs (`X86Compiled`) are used by both and counted in both columns. Against the ISWIM pipeline's plain graph model:

| adequacy of the graph model (reported separately) | ISWIM pipeline: CEK machines | ISWIMμ: CEK machines (alternative) | ISWIMμ: interpreters |
|---|---:|---:|---:|
| ISWIM: the source (typed: untyped ISWIM's machine, shared with the untyped pipeline) | 653 | 467 | **395** |
| Clos5: the values of its machine or interpreter and the tables, which X86 adequacy uses (typed: also the adequacy of the Clos5ᵀ machine) | 715 | 307 | **301** |
| X86: the target, direct | **679** | 697 | 712 |
| well-formedness of compiled programs | 41 | **35** | **35** |
| end to end | 33 | 22 | **15** |
| shared modules not used by all four proofs, nor by the graph model | **69** | **69** | **69** |
| the ISWIM pipeline's modules μ reuses (meaning of the primitives, framework instances), nor by the graph model | — | 2 | 2 |
| **total** | 2190 | 1599 | **1529** |

Counted in ISWIMμ's adequacy: `Mu.proof.Compiler.GlobalizeOlder` (54), `Semantics.Interp.Clock` (+ proof/) (2), `Semantics.Observation` (15); in the alternative, `Semantics.CEK.Smallstep` (+ proof/) (2) for the clock's instance.

* **Interpreters against machines: 1599 → 1529 (−4%).** Evaluation is "returns v from some clock on" (`Stable`), as in the mixing experiment's bridge, which is now ISWIMμ's adequacy (see [[#Mixing semantics]]): results compose by `st-bind`, and determinism is `stable-unique` (no `Ret`, `Retq`, `Ret-det`, `↠-final-det` or runs of a step function: `proof/Framework/Runs.agda` leaves adequacy's infrastructure). Soundness is by induction on the clock (and the term, or the blocks and the sequence) instead of over the steps of a machine, so it has no continuations or call stack, and its result predicate excludes `error`, so neither half needs a no-error lemma (the end theorem gets divergence from the emptiness of the denotations, `diverges-iff`).
  * ISWIM 467 → 395: soundness 242 → 174 (no `𝒦`, `𝒦-mono`, `halts` or `step-⊆`), the logical relation 128 → 121.
  * Clos5 307 → 301: the values of the Clos5μ interpreter (`Clos5Values`, which the X86μ interpreter shares) instead of the Clos5μ machine's; `obs-answer` is not needed (no convergence statements). `lvl<` moved to `Clos5Common`, which both use.
  * X86 697 → 712 (+15). The fundamental lemma is smaller (`X86LogRel` 199 → 169: an instruction is one recursive call of the interpreter, so no step lemma `⇐`, and no `Retq`); `X86Common` keeps only `OpR` (10 → 4). Soundness is larger (470 → 499): without a call stack, a call's soundness combines the callee's approximations of its start, one per element of the finite part of the result the caller uses, into one (`merge`, by `grow-each`), where the machine carries one approximation down the stack (`𝒦`); and every case names the next state. The statements (`X86.agda`, 18 → 40) give divergence and need the results' lemmas the CEK version got from `Terminates`.
  * End to end 22 → 15: the two adequacy theorems and `compile-x86-same` compose directly into the interpreter column's `compile-x86-const` and `compile-x86-diverges`, with no lemma that a machine that does not converge diverges.

The comparisons with the ISWIM pipeline below are of the CEK-machine version (the alternative column), which has the same target as the ISWIM pipeline's.

* **The logical relation carries over unchanged.** It is by recursion on the denotational value, as the ISWIM pipeline's, with `𝕍 d (fold v) = 𝕍 d v`; `fold` and `unfold` are identities in the denotations of values, continuations and states, so soundness has one line for each. Since the machines are typed, there is no `ShapeOf` and no case for a value of the wrong kind: an observation is read off the related value (`𝕍-const`, `obs-answer`), as in the ISWIM pipeline's Clos5ᵀ adequacy.
* **ISWIM 653 → 467.** The ISWIM pipeline's source adequacy is for untyped ISWIM (kind errors, `ShapeOf`, unbound variables), and gets the monotonicity, continuity and consistency of the semantics from the generic-signature framework. ISWIMμ's semantics is a function on intrinsically typed terms, so these are proved by induction on the term (`Mu/proof/Semantics/Graph/ISWIM.agda`, 20, as for Clos5μ; in the graph model's semantics row, since simplify's proof uses them too), and the tuples of sets (`Tuples`, 74) are a copy of the part of the ISWIM pipeline's ISWIM soundness that X86 adequacy also uses, so that ISWIMμ depends on no adequacy module of the ISWIM pipeline.
* **No Clos5μ adequacy.** The ISWIM pipeline's Clos5ᵀ adequacy (its machine's fundamental lemma and soundness: `Clos5LogRel` 97, `Clos5` 29 and most of `Clos5Soundness`' 231) serves only the end-to-end statements into the Clos5ᵀ machine; the end-to-end theorem into X86 is direct. ISWIMμ ports only what X86 adequacy uses: the values of the Clos5μ machine in the graph model (`Clos5Values`, 237 against 293, without tags and `proj?`) and the table lemmas (`Clos5Common`, 70, with `tbl-mono` and `olderAt` from the ISWIM pipeline's `Clos5Soundness`). Like for like, the ISWIM pipeline's adequacy into X86ᵀ alone is about 1870.
* **X86 679 → 697 (+18).** `chk`, `testinl`, `je` and the field reads go; `case` (`choose` against 𝒞 in adequacy, a slot write of the payload in soundness), the `↓` operand and bodies indexed by their result type come (`Ret`, the stack and `AdeqB` carry the type, and `Ret-det` compares pairs of a type and a value); the open closure is related to its slot by a datatype (`OpR`: X86μ's machine keeps the environment and its types η, not the code).
* **Well-formedness of compiled programs**: as in the ISWIM pipeline, the table of `compile-x86 M` is consistent and contains each definition's code with the whole table (`X86Compiled`, 35), from globalize's references to older definitions only (`Mu/proof/Compiler/GlobalizeOlder.agda`, 54, a shared module, counted in the adequacy total with the observations).
* **The graph model with errors has no counterpart.** In the ISWIM pipeline it exists to observe errors: the plain graph model denotes an error and divergence alike by ∅. ISWIMμ has no error to observe, and soundness shows that the interpreters never err, so the plain graph model with adequacy states the operational theorem. The ISWIM pipeline's adequacy with errors (2281, and the 2126 lines of the CEK proof it derives Clos5ᵀ adequacy from) has nothing left to do.

### No-error lemmas

In no total: no semantics of ISWIMμ or X86μ stops with an error. By typing, none has an error case but the reduction semantics' catch-alls; nothing was removed.

| no-error lemmas (not in any total) | lines |
|---|---:|
| CEK machines of ISWIMμ and X86μ (X86μ's is also the reduction column's) | 68 |
| clocked interpreters of ISWIMμ and X86μ | 87 |
| reduction semantics of ISWIMμ | 44 |
| **total** | 199 |

* **Needed by no end-to-end theorem.** The graph model's, through adequacy for the interpreters, gets divergence from soundness, which shows the interpreters never err. Only the alternative adequacy for the CEK machines uses the CEK machines' (`Mu/proof/Semantics/CEK/NoError.agda`, for its divergence statement; no longer stated in `Mu/Theorems/Adequacy.agda`). They are by inspection of the step function: a machine stops only at the empty continuation (stack), and no value is observed as `o-error` (most of the 68 lines are the cases of `step`, one per line).
* **The interpreters** (`Mu/proof/Semantics/Interp/NoError.agda`) have no `error` result either; the lemma follows their recursion (a result is `Safe` at every clock).
* **The reduction semantics** (`Mu/proof/Semantics/Reduction/NoError.agda`) has catch-all error cases: each redex splits its operand at a generic type with an equation (`β : Tm [] C → C ≡ A ⇒ B → …`; the green slime of `unfold`'s index), and `obs` is `o-error` on a term that is not a value. They are unreachable, by progress: a closed term is a value or reduces, and a value of a function, tuple, sum, integer or recursive type has the form of its type (the cases of `Value` at that type). Removing them would need the redexes to take values, not terms, so they stay.

### Infrastructure

Language-independent infrastructure by use, not in any total (see [[#Language-independent infrastructure]]); each proof column is the part of a group that the proof reaches, and adequacy's column counts only what the graph model does not use:

| language-independent infrastructure (ISWIMμ, not in the totals) | lines | used by denotational: graph model | used by CEK machine + simulation | used by clocked interpreter + value relations | used by reduction semantics + simulation | used by adequacy |
|---|---:|---:|---:|---:|---:|---:|
| abstract binding trees | 190 | 170 | — | — | 61 | — |
| syntax lemmas (renaming, scoping, uses, substitution), list lookups | 519 | 9 | 9 | 9 | 397 | — |
| base types, logical equivalence | 58 | 20 | 20 | 20 | 20 | — |
| typed indices, lookup in typed lists, vectors (collecting, selecting, projecting) | 130 | 57 | 57 | 57 | 57 | — |
| denotational framework | 375 | 200 | — | — | — | — |
| graph model: values, consistency, machinery for any operators | 364 | 276 | — | — | — | — |
| graph model: its operators | 623 | 608 | — | — | — | — |
| graph model: semantics of intrinsically typed syntax | 237 | 126 | — | — | — | — |
| small-step framework: transition systems, simulations | 273 | — | 273 | — | 273 | — |
| reduction framework: reduction semantics, simulations between them | 254 | — | — | — | 254 | — |
| clocked big-step framework | 249 | — | — | 249 | — | 249 |
| heterogeneous vectors: lookup, collecting, selecting, relating (ISWIMμ's) | 88 | 78 | 88 | 78 | 88 | 10 |
| reduction of heterogeneous vectors (ISWIMμ's) | 41 | — | — | — | 41 | — |
| **total** | — | 1544 | 447 | 413 | 1191 | 259 |

ISWIMμ's own infrastructure is heterogeneous vectors (`Mu/Framework/AllUtil.agda` and its lemma `Mu/proof/Framework/AllProp.agda`) and the reduction of their operands (`Mu/Framework/ReductionAll.agda` and its `proof/` half), as `Framework/VecUtil.agda`, `VecSelect.agda` and `ReductionVec.agda` are for vectors.

### Audit-surface counts

The lines a reader must audit to trust each style's theorems (see [[#Audit surface]]), not in the totals: the shared part (languages, passes, syntax, base types, typed indices, heterogeneous vectors, observations), counted once in the first column, the semantics of each style, and its theorem statements (`agda/Mu/Theorems/`). The machines of Clos5μ, Impμ, CFGμ and X86μ are read for both the CEK and the reduction statements, so they appear in both semantics rows; the adequacy statements read the graph model and the interpreters of ISWIMμ and X86μ.

| audit surface (ISWIMμ) (not in the totals) | lines | read for denotational: graph model | read for CEK machine + simulation | read for clocked interpreter + value relations | read for reduction semantics + simulation | read for adequacy |
|---|---:|---:|---:|---:|---:|---:|
| languages, compiler passes, syntax, base types (shared) | 1164 | 1124 | 1084 | 1084 | 1128 | 1150 |
| graph model: domain, operators, semantics of each language | 348 | 348 | — | — | — | 348 |
| simulation: small-step machines, transition systems | 547 | — | 547 | — | 308 | — |
| interpreter: clocked interpreters, results | 346 | — | — | 346 | — | 256 |
| reduction: reduction semantics, machines of the first-order languages, transition systems | 757 | — | 308 | — | 757 | — |
| graph model: theorem statements | 76 | 76 | — | — | — | — |
| simulation: theorem statements | 38 | — | 38 | — | — | — |
| interpreter: theorem statements | 38 | — | — | 38 | — | — |
| reduction: theorem statements | 38 | — | — | — | 38 | — |
| adequacy: theorem statements | 19 | — | — | — | — | 19 |
| **total** | 3063 | 1548 | 1669 | **1468** | 1923 | 1773 |

The adequacy statements also use ρ₀ from the denotational ones (Mu/Theorems/Denotational.agda), not counted in its column.

* **The interpreter's surface is the smallest** (1468), then the graph model's (1548), CEK (1669) and reduction (1923); in the ISWIM pipeline the graph model's is the smallest (1649, against 1664 for the interpreter; see [[#Audit-surface counts (ISWIM)]]). Every style reads less than in the ISWIM pipeline (−101, −295, −196, −220; adequacy, now for the interpreters, 2024 → 1773): no `Any`, tags, `project` or its guard and check, no cast insertion and closedness, and no errors in the semantics, against `fold`/`unfold`, μ types and heterogeneous vectors.
* **The graph model's statements are the longest** (76, against 38): `≃` and delay's `Same` written out for each pass and each prefix of the compiler, and the end-to-end theorem for `main : Int`, whose operational form is the adequacy file's.

### Shared modules

| shared module (ISWIMμ) | lines | used by |
|---|---:|---|
| `Language.Prim` | 10 | all four proofs |
| `Language.Reg` | 3 | all four proofs |
| `Mu.Compiler.Concretize` | 38 | all four proofs |
| `Mu.Compiler.Delay` | 25 | all four proofs |
| `Mu.Compiler.Enclose` | 18 | all four proofs |
| `Mu.Compiler.Explicate` | 33 | all four proofs |
| `Mu.Compiler.Globalize` | 53 | all four proofs |
| `Mu.Compiler.LiftLocals` | 16 | all four proofs |
| `Mu.Compiler.Optimize` | 80 | all four proofs |
| `Mu.Compiler.Pipeline` | 13 | all four proofs |
| `Mu.Compiler.RCO` | 39 | all four proofs |
| `Mu.Compiler.Select` | 58 | all four proofs |
| `Mu.Compiler.Simplify` | 151 | all four proofs |
| `Mu.Language.CFG` | 30 | all four proofs |
| `Mu.Language.Clos2` | 15 | all four proofs |
| `Mu.Language.Clos3` | 15 | all four proofs |
| `Mu.Language.Clos4` | 16 | all four proofs |
| `Mu.Language.Clos5` | 49 | all four proofs |
| `Mu.Language.ISWIMSubst` | 31 | all four proofs |
| `Mu.Language.ISWIM` | 15 | all four proofs |
| `Mu.Language.Imp` | 22 | all four proofs |
| `Mu.Language.Mon` | 50 | all four proofs |
| `Mu.Language.Type` | 52 | all four proofs |
| `Mu.Language.X86` | 102 | all four proofs |
| `Mu.proof.Compiler.GlobalizeOlder` | 54 | adequacy |
| `Semantics.Observation` | 15 | simulation, interpreter, reduction, adequacy |

| the ISWIM pipeline's module reused by ISWIMμ | lines | used by |
|---|---:|---|
| `Semantics.CEK.Smallstep` (+ proof/) | 2 | simulation, reduction |
| `Semantics.Graph.Prim` (+ proof/) | 34 | graph model, adequacy |
| `Semantics.Interp.Clock` (+ proof/) | 2 | interpreter, adequacy |
| `Semantics.Reduction.Smallstep` | 1 | reduction |
| `proof.Semantics.CEK.Simulation` | 1 | simulation, reduction |

| infrastructure module (ISWIMμ) | lines | used by |
|---|---:|---|
| `Framework.Clocked` (+ proof/) | 249 | interpreter, adequacy |
| `Framework.GraphModel.DOpSig` (+ proof/) | 46 | graph model, adequacy |
| `Framework.GraphModel.Domain` (+ proof/) | 70 | graph model, adequacy |
| `Framework.GraphModel.Env` (+ proof/) | 84 | graph model, adequacy |
| `Framework.GraphModel.OpsBase` (+ proof/) | 36 | graph model, adequacy |
| `Framework.GraphModel.Ops` (+ proof/) | 324 | graph model, adequacy |
| `Framework.GraphModel.SetsAsPredicates` (+ proof/) | 56 | graph model, adequacy |
| `Framework.Iff` | 3 | graph model, simulation, interpreter, reduction, adequacy |
| `Framework.ListUtil` (+ proof/) | 114 | reduction |
| `Framework.Lookup` (+ proof/) | 37 | graph model, simulation, interpreter, reduction, adequacy |
| `Framework.Membership` | 20 | graph model, simulation, interpreter, reduction, adequacy |
| `Framework.Primitives` | 17 | graph model, simulation, interpreter, reduction, adequacy |
| `Framework.ReductionVec` (+ proof/) | 19 | reduction |
| `Framework.Reduction` (+ proof/) | 235 | reduction |
| `Framework.Smallstep` (+ proof/) | 127 | simulation, reduction |
| `Framework.Syntax.Kit` | 9 | graph model, simulation, interpreter, reduction, adequacy |
| `Framework.Syntax.Rename` (+ proof/) | 59 | reduction |
| `Framework.Syntax.Scope` (+ proof/) | 32 | reduction |
| `Framework.Syntax.SigUtil` | 4 | graph model, reduction, adequacy |
| `Framework.Syntax.Subst` (+ proof/) | 139 | reduction |
| `Framework.Syntax.SyntaxUtil` | 6 | reduction |
| `Framework.Syntax.Uses` (+ proof/) | 44 | reduction |
| `Framework.abt.AbstractBindingTree` | 14 | reduction |
| `Framework.abt.GSubst` | 7 | graph model, reduction, adequacy |
| `Framework.abt.ScopedTuple` (+ proof/) | 129 | graph model, adequacy |
| `Framework.abt.Sig` | 16 | graph model, reduction, adequacy |
| `Framework.abt.Var` | 14 | graph model, reduction, adequacy |
| `Mu.Framework.AllUtil` | 78 | graph model, simulation, interpreter, reduction, adequacy |
| `Mu.Framework.ReductionAll` (+ proof/) | 41 | reduction |
| `Mu.proof.Framework.AllProp` | 10 | simulation, reduction, adequacy |
| `proof.Framework.Both` | 30 | simulation, reduction |
| `proof.Framework.GraphModel.ContinuityBase` | 99 | graph model, adequacy |
| `proof.Framework.GraphModel.Continuity` | 135 | graph model, adequacy |
| `proof.Framework.GraphModel.DenotProperties` | 14 | graph model, adequacy |
| `proof.Framework.GraphModel.DomainUtilBase` | 71 | graph model, adequacy |
| `proof.Framework.GraphModel.DomainUtil` | 15 | graph model, adequacy |
| `proof.Framework.GraphModel.Laws` | 83 | graph model, adequacy |
| `proof.Framework.GraphModel.Strict` | 51 | graph model, adequacy |
| `proof.Framework.GraphModel.TypedGraph` | 34 | graph model, adequacy |
| `proof.Framework.GraphModel.TypedOkBase` | 92 | graph model, adequacy |
| `proof.Framework.Simulation` | 116 | simulation, reduction |

Examples, not counted: 53 lines.

Module (+ proof/): the definitions are on the audit surface, the lemmas in its proof/ half; the lines are those of both.

### Scott domains

The fifth column, a second denotational proof with Scott domains (`loc.py --scott`; `make check-scott`, which needs TypeTopology, so the column is not in `make check` or the four-column tables above). It has the same rows as the graph model, and its semantics row counts the meaning of the primitives, as the graph model's does. After the opaque `inj`/`case` (PR #93) and the cleanup (PR #95), a clean `make check-scott`, TypeTopology included, takes about 2.5 minutes.

| component (ISWIMμ) | denotational: graph model | denotational: Scott domains |
|---|---:|---:|
| semantics of the languages | 427 | **395** |
| lemmas shared by the passes | — | 135 |
| simplify | **349** | 411 |
| CC: enclose | **37** | 49 |
| CC: optimize | **66** | 92 |
| CC: concretize | **46** | 58 |
| CC: delay | **450** | 723 |
| CC: globalize | **115** | 147 |
| rco | **109** | 159 |
| lift locals | **39** | 59 |
| explicate control | **64** | 92 |
| select instructions | **76** | 133 |
| composition | **28** | 32 |
| **total** | **1806** | 2485 |

Counted in the graph model's semantics row: `Semantics.Graph.Prim` (+ proof/) (34).

The Scott column counts the meaning of the primitives (`Semantics.Scott.Prim`) in its semantics row, and simplify's syntactic lemmas (`Mu.proof.Compiler.SimplifyFacts`) in its simplify row, as the graph model does; its delay row includes the calls of approximated closures (`proof.Framework.Scott.StageCall`).

| infrastructure of the Scott column (not in the total) | lines |
|---|---:|
| dcpos on TypeTopology: exponentials, products, powers, sums, lifting | 471 |
| locally continuous functors, the solution of D ≅ F D as a bilimit | 389 |
| the domain of values and its operators | 361 |
| combinators for continuous meanings | 155 |
| the stages of the bilimit (approximations by depth) | 131 |
| **total** | 1507 |

Theorem statements (Mu/Theorems/Scott.agda): 84 lines.

TypeTopology itself (not counted anywhere): the Scott column imports, transitively from `agda/AllScott.agda`, 80 TypeTopology modules with about 18,600 lines of code (the `code` blocks of the `.lagda` files, without comments, blank lines or imports; counted 2026-10-22 at the pinned commit). The paper's §3 quotes this figure.

* **Total:** 2485, 1.4 times the graph model (1.3 by tokens), larger in every row but the semantics.
* **Delay (723 against 450):** one stage-indexed relation `R δ n s w` over a direction δ serves both halves (`DelayRel.agda`). By category, out of 838 comment-stripped lines with imports: the relation's definitions, is-prop, monotonicity, admissibility and the moves between stages 174; calls 101 and `StageCall` 198 (299, the largest share: a call of a pair seen at stage m + 2 shows its result only at stage m); primitives and tagged values 71 (about a twelfth); closures 43, other operators 62, terms and top level 66, header and imports 123.
* **Remaining workarounds for slow `with`** (slow whenever a value of 𝔻 or an environment is in scope): the -res/-eq lemmas and `kfun` in simplify, `th-cons` in optimize, the records OK/OKs/Cong₁/Cong₂ and `programO` in globalize, Out projections in explicate control, and the opaque `db` and `Start` module in select instructions.

## Dynamic typing and errors

The ISWIM pipeline (`agda/`; in full in [[#The ISWIM pipeline in full]]) compiles untyped ISWIM: cast insertion makes every check of the kind of a value explicit as a `project` from the type `Any` of tagged values, and the languages after it are intrinsically typed, down to X86ᵀ, whose only check is `project`'s, `chk`. So it differs from ISWIMμ by dynamic typing (`Any`, the tags, `project` and its failure, the error observation, and the cast-insertion pass) and by how recursion is typed (ISWIM's self-application through `Any`, ISWIMμ's through iso-recursive types). Its fifth column, the graph model with errors, observes errors denotationally. Per style (`loc.py`; the same rows as the ISWIM pipeline's main table, [[#Counts of the ISWIM pipeline]]):

| per style | graph model | simulation | interpreter | reduction | graph model with errors |
|---|---:|---:|---:|---:|---:|
| ISWIM pipeline, total | 2131 | 2582 | 1814 | 3620 | 2613 |
| ISWIM pipeline, total without cast insertion | 2064 | 2390 | 1719 | 3320 | 2488 |
| ISWIMμ, total | 1806 | 2103 | 1504 | 3093 | — |
| ISWIM pipeline: simplify | 342 | 574 | 640 | 716 | 348 |
| ISWIMμ: simplify | 349 | 560 | 508 | 697 | — |
| ISWIM pipeline: delay | 552 | 99 | 35 | 142 | 801 |
| ISWIMμ: delay | 450 | 73 | 35 | 126 | — |

| adequacy (reported separately) | graph model | graph model with errors |
|---|---:|---:|
| ISWIM pipeline | 2190 | 2281 |
| ISWIMμ | 1529 | — |

* **Dynamic typing, with recursion held constant, costs every style little, and does not change the ranking.** Like for like (without cast insertion, which ISWIMμ does not need), ISWIMμ is 12.5%, 12%, 12.5% and 7% smaller (2064 → 1806, 2390 → 2103, 1719 → 1504, 3320 → 3093); counting cast insertion (67, 192, 95, 300), 15%, 19%, 17% and 15%. Most of that is the final cleanup pass, which only ISWIMμ's proofs had (PRs #87–#91: 155, 155, 149 and 114 lines): before it, like for like, ISWIMμ was 5%, 6%, 4% and 3% smaller (1961, 2258, 1653, 3207). The ranking is the same: interpreter < graph model < CEK < reduction. Simplify, which both have, cost about the same in both before the cleanup (360, 584, 633, 715 against 342, 574, 640, 716; see [[#Current counts]]). What goes: `project` and its failure, the `inject`/`dyn` values and the tags, and the error cases of the machines, interpreters and reduction semantics; what comes: `fold`/`unfold` (a congruence per pass) and heterogeneous vectors. Of the graph model's difference, 49 lines are select's proof that X86ᵀ's `testinl`, payload load and `je` agree with CFGᵀ's `case`, which X86μ makes one typed pseudo-instruction (no state type can give the payload's slot both the left and the right type between the load and the jump). Row by row: `loc.py --mu-detail`.
* **Errors cost the graph model a fifth column.** The plain graph model denotes an error and divergence alike by ∅, so in the ISWIM pipeline only the graph model with errors (an error denotes a set holding ω) states the operational theorem, at 2613 lines against 2131 (2488 against 2064 without cast insertion; delay 801 against 552), with its own adequacy (2281, derived in part from the CEK column). ISWIMμ has no errors: adequacy for the interpreters gives divergence directly (soundness shows they never err), and the plain graph model with adequacy states the operational theorem (see [[#Adequacy]]). So ISWIMμ needs no graph model with errors. See [[#Graph model with errors]].
* **Without errors, delay barely moves: 552 → 524 in the graph model before the final cleanup pass** (99 → 96, 35 → 35 and 142 → 139 in the others). The cleanup (PRs #89–#91) then took ISWIMμ's delay to 450, 73, 35 and 126 without changing the relation: in the graph model, `Approx D D'` (D is related to every finite part of D', the form of the fundamental lemma, with `Approx-const`, `Approx-ne` and `Approx-untag`) and `Approx-fold` (the four clauses, for every finite part of D') replace a set of single-use lemmas, so `DelayRel` grows and `DelayPreserve` and `DelayReflect` shrink. Its cost is not caused by errors or dynamic typing. What disappeared: only `fun-obs`, the clause of the approximant logical relation for `project`, and the cases of the proofs that go with it. What stayed: the approximant logical relation and its depth index, which recursive types need (a relation by recursion on the type would define it at `μ A` as at `A [ μ A ]`, not smaller; at `μX. X ⇒ Int`, `app-obs` asks for the relation at the same type). By module (ISWIMμ's after the cleanup):

| graph-model delay, by module | ISWIM pipeline | ISWIMμ |
|---|---:|---:|
| `DelayRel` | 132 | 144 |
| `DelayPreserve` | 159 | 134 |
| `DelayReflect` | 252 | 163 |
| `DelayCorrect` | 9 | 9 |
| **total** | 552 | 450 |

* **Adequacy 2190 → 1599** for the CEK machines (ISWIMμ's alternative), of which about 320 is the Clos5ᵀ machine's adequacy, which ISWIMμ does not need; like for like (into X86 alone) about 1870 → 1599. ISWIMμ's adequacy for the interpreters is 1529.
* **What ISWIMμ settled** (`notes/iswim-mu-design.md`, notes [P0]–[P3]): `unfold` needs no equation (no definition splits a term at a concrete type); heterogeneous contexts cost nothing net (optimize's renaming is defined on the used variables, `squeeze`); the existential of X86μ's closures hides a `Ctx` at no cost; no pass after delay looks at μ.

## Mixing semantics

The question: each pass has a cheapest style, so is the compiler cheaper to prove if each pass is proved in the cheaper of the graph model and the interpreter, with the styles joined by **bridges**? A bridge is an adequacy theorem between a language's graph semantics and its interpreter, built wherever the style changes. Design and estimates: `notes/mixed-semantics.md`.

Only three passes are cheaper in the graph model: simplify (349 against 508), globalize (115 against 175) and explicate control (64 against 75).

* **Split (a)** proves simplify in the graph model and every other pass by the interpreters. It needs one bridge, at ISWIMμ, used twice: for the program and for its simplification. The bridge is ISWIMμ's adequacy for its interpreter (`Mu/proof/Adequacy/ISWIM.agda` with `Soundness`, `LogRel` and `Tuples`), shared with the graph model's adequacy; the experiment's own module is the composition (`Mu/proof/Mixed/CompilerMixed.agda`).
  * The chain: interpreter(M) ⇔ ⟦M⟧ ⇔ ⟦simplify M⟧ ⇔ interpreter(simplify M) ⇔ X86μ interpreter(compile-x86 M).
  * Its end theorem is the interpreter column's (`Mu/proof/Mixed/CompilerMixed.agda`: `compile-x86-const`, `compile-x86-diverges`).
  * It reuses the per-pass proofs of both columns unchanged.
* **Splits (b) and (c)** also prove globalize and/or explicate control in the graph model. They need two more bridges for each pass (at Clos4μ and Clos5μ, at Impμ and CFGμ). They are estimated, not built: each further bridge is counted at the size of ISWIMμ's.

`loc.py` (the full tables with `--mixed`):

| proof of the ISWIMμ compiler | passes in the graph model | bridges | total | end theorem about |
|---|---|---:|---:|---|
| denotational: graph model | all | — | 1806 | denotations |
| CEK machine + simulation | — | — | 2103 | the machines |
| clocked interpreter + value relations | — | — | **1504** | the interpreters |
| reduction semantics + simulation | — | — | 3093 | the reduction semantics |
| denotational: graph model, and its adequacy | all | — | 3335 | the interpreters |
| denotational: graph model, and its adequacy for the CEK machines (alternative) | all | — | 3405 | the machines |
| mixed (a) simplify in the graph model | simplify | 1 | 1838 | the interpreters |
| mixed (b) also globalize (estimate) | simplify, globalize | 3 | ~2532 | the interpreters |
| mixed (b) also explicate control (estimate) | simplify, explicate control | 3 | ~2585 | the interpreters |
| mixed (c) the per-pass minimum: also globalize and explicate control (estimate) | simplify, globalize, explicate control | 5 | ~3260 | the interpreters |

Split (a), row by row, against the two columns it draws on:

| component (ISWIMμ) | mixed (a): proved by | mixed (a) | graph model | interpreter |
|---|---|---:|---:|---:|
| semantics: interpreters (all languages) | interpreter | 374 | — | 374 |
| semantics: graph model (ISWIMμ only) | graph model | 58 | 393 | — |
| simplify | graph model | 349 | 349 | 508 |
| CC: enclose | interpreter | 33 | 37 | 33 |
| CC: optimize | interpreter | 65 | 66 | 65 |
| CC: concretize | interpreter | 42 | 46 | 42 |
| CC: delay | interpreter | 35 | 450 | 35 |
| CC: globalize | interpreter | 175 | 115 | 175 |
| rco | interpreter | 83 | 109 | 83 |
| lift locals | interpreter | 27 | 39 | 27 |
| explicate control | interpreter | 75 | 64 | 75 |
| select instructions | interpreter | 48 | 76 | 48 |
| bridge at ISWIMμ (ISWIMμ's adequacy, shared with the graph model's) | — | 395 | — | — |
| composition | — | 28 | 28 | 22 |
| shared modules not used by all four proofs | — | 15 | — | 15 |
| the ISWIM pipeline's modules it reuses (meaning of the primitives, framework instances) | — | 36 | 34 | 2 |
| **total** | — | **1838** | 1806 | 1504 |
| language-independent infrastructure used (not in the totals) | — | 1573 | 1544 | 413 |

The bridge at ISWIMμ is ISWIMμ's adequacy with respect to its interpreter, the ISWIM row of [[#Adequacy]]. It is smaller than the alternative with respect to the CEK machine:

| ISWIMμ adequacy | w.r.t. the CEK machine (alternative) | w.r.t. the interpreter (the bridge) |
|---|---:|---:|
| soundness | 242 | **174** |
| logical relation, fundamental lemma | 128 | **121** |
| statements (constants, convergence or divergence) | **23** | 26 |
| tuples of sets (`Mu.proof.Adequacy.Tuples`, the same module) | 74 | 74 |
| **total** | 467 | **395** |

* **Mixing does not pay on ISWIMμ.**
  * Split (a) is 1838 lines, 334 more than the interpreter column (1504).
  * Simplify saves 159 lines (508 → 349).
  * The composition costs 6 more (28 against 22).
  * The bridge (395) and ISWIMμ's graph semantics (58, with the binder congruences) and primitives (34) cost 487.
  * Split (a) also uses almost all of the graph model's infrastructure (1573 against the interpreter's 413), which is in no total.
  * The other passes that are cheaper in the graph model save 60 (globalize) and 11 (explicate control). Each needs two more bridges, so (b) and (c) are far worse: about 2500–3300.
  * A bridge costs as much as a pass's whole proof, so mixing pays only for a pass whose saving exceeds the bridges it needs. On this compiler only simplify saves more than a few dozen lines, and it falls far short (159 against 487).
* **The bridge is counted once.** Each total in the table above stands alone: split (a)'s 1838 counts the bridge (395) once, in its own row, and is not added to adequacy's; the graph model's 3335 counts it once too, in adequacy's ISWIM row. The two proofs share it, as the graph model and the interpreter column share nothing else.
* **Against the graph model, mixing is a real gain.** Split (a) reaches running code (the interpreters) at 1838, against the graph model's 3335 with adequacy (the same interpreters; 3405 with the alternative for the machines). It keeps the graph model's proof of simplify, its cheapest by far, and avoids the graph model's delay (450 against 35).
* **The bridge is cheaper than adequacy for the machine.**
  * Soundness is by induction on the clock and the term, with no continuations: 174 against 242.
  * The logical relation uses results stable from some clock on (`Stable`, `st-bind`), so it needs no monotonicity lemma. Its determinism is `stable-unique`: 121 against 128.
  * Soundness also shows that the interpreter never errs (the result predicate excludes `error`), so the bridge needs no no-error lemma.
  * So ISWIMμ adequacy with respect to the interpreter is 395 lines, against 467 with respect to the CEK machine (−15%). This is why adequacy was moved to the interpreters (see [[#Adequacy]]): for X86μ the gain does not carry over (712 against 697).
* **What each end theorem includes.**
  * The graph column's end theorem (`compile-x86-same`) is about denotations. It reaches running code only with adequacy (1529, for the interpreters, reported separately).
  * The operational columns' end theorems, and split (a)'s, are about running code already: the machines, the interpreters, the reduction semantics.
  * The audit surface of split (a) is the interpreter column's plus ISWIMμ's graph semantics and the graph model's domain and operators. The bridge's statement mentions them, although the end theorem does not.

## The ISWIM pipeline in full

The ISWIM pipeline's tables (`loc.py --iswim`). Its compiler, `compile-x86` (`agda/Compiler/Pipeline.agda`), runs

    ISWIM --simplify--> ISWIM --cast insertion--> ISWIMᵀ --enclose--> Clos2ᵀ --optimize--> Clos2ᵀ
          --concretize--> Clos3ᵀ --delay--> Clos4ᵀ --globalize--> Clos5ᵀ --rco--> Monᵀ
          --lift locals--> Impᵀ --explicate control--> CFGᵀ --select instructions--> X86ᵀ

The source, ISWIM, is untyped. Since PRs #55 and #56 the intermediate languages are intrinsically typed (`agda/Language/Typed/`), after *Essentials of Compilation*, ch. 9: cast insertion makes every check of the kind of a value explicit, as a `project` from the type `Any` of tagged values, placed where the ISWIM machine performs the check. In every later language `project` is the only operation that can fail. Since PR #58 the target is X86ᵀ (`agda/Language/Typed/X86.agda`), a typed assembly language after Morrisett, Walker, Crary and Glew's TAL: x86 with variables over abstract values, its instructions typed by the types of the registers, the frame, the open closure and the flag they start and end with; its only check is `project`'s, `chk`, which stands for the X86 instruction that errs on a value of another kind. Erased, X86ᵀ is untyped X86, the target of the untyped pipeline (see [[#Assurance]]). Simplify (since PR #40) is a source optimizer on untyped ISWIM. The prefixes of the compiler, `compile₄` (into Clos4ᵀ), `compile` (Clos5ᵀ), `compile-mon` (Monᵀ, run as its embedding into Clos5ᵀ), `compile-imp` (Impᵀ) and `compile-cfg` (CFGᵀ), are each proved end to end too. Its five columns:

* **Denotational: graph model**: in `agda/Semantics/Graph/` (ISWIM) and `agda/Semantics/Graph/Typed/` (the typed languages, X86ᵀ among them; the proofs under `agda/proof/Correctness/Graph/`, the lemmas about the semantics under `agda/proof/Semantics/Graph/`). A failed `project`, like any error, means ∅. The theorem (`Theorems/Denotational.agda`): every pass but delay preserves the meaning exactly (≃); delay preserves and reflects constants and nonemptiness; so the compiled program produces the same constants as the source, and produces something exactly when the source does.
* **CEK machine + simulation**: in `agda/Semantics/CEK/` and `agda/Semantics/CEK/Typed/` (the proofs under `agda/proof/Correctness/CEK/`). The theorem (`Theorems/Simulation.agda`, end to end `PipelineSim`): the two programs terminate with the same observation, including an error, and one diverges exactly when the other does.
* **Clocked interpreter + value relations**: in `agda/Semantics/Interp/` and `agda/Semantics/Interp/Typed/` (the proofs under `agda/proof/Correctness/Interp/`). The theorem (`Theorems/Interpreter.agda`) has the same shape as the simulation one.
* **Reduction semantics + simulation**: in `agda/Semantics/Reduction/` and `agda/Semantics/Reduction/Typed/` (the proofs under `agda/proof/Correctness/Reduction/`), with the substitution library `agda/Framework/Syntax/Subst.agda`. The theorem (`Theorems/Reduction.agda`) has the same shape as the simulation one.
* **Graph model with errors** (the fifth column): a graph-model semantics in which an error denotes a set that holds ω and divergence denotes ∅, built from an error monad on 𝒫 Value (`agda/Framework/GraphModel/ErrorMonad.agda`), in `agda/Semantics/GraphErr/` and `agda/Semantics/GraphErr/Typed/` (the proofs under `agda/proof/Correctness/GraphErr/`). The theorem (`Theorems/GraphErrors.agda`): every pass but delay preserves the meaning exactly, errors included (select too, since PR #58); delay preserves and reflects an error, the constants and having a value; and, with adequacy, the ISWIM machine and the X86ᵀ machine on the compiled program stop with an error together, stop with the same constants, stop with an answer together and diverge together. See [[#Graph model with errors]].

What both ISWIM pipelines use (untyped ISWIM and simplify with its four proofs, the primitives, the observations, and the ISWIM adequacy) is in groups of both, and is counted in full in each. The assurance that X86ᵀ is faithful to untyped X86 is in no total (see [[#Assurance]]).

### Counts of the ISWIM pipeline

As of PR #58 (the target of the typed pipeline is the typed assembly language X86ᵀ, in every column; see [[#History]], [[#Typed assembly language]] and [[#Typed against untyped]]). The last column is the graph model with errors, counted as the four are (plus the graph model's meaning of the primitives, which it extends) but not in their comparison: the shared modules not counted are still those all four use. The closure-conversion passes (enclose, optimize, concretize, delay, globalize) are labelled "CC: " in the tables, since simplify, cast insertion, rco and the later passes are not part of closure conversion:

| component | denotational: graph model | CEK machine + simulation | clocked interpreter + value relations | reduction semantics + simulation | graph model with errors |
|---|---:|---:|---:|---:|---:|
| semantics of the languages | 450 | 674 | **442** | 1066 | 518 |
| lemmas shared by the passes | — | 20 | — | — | — |
| simplify | **342** | 574 | 640 | 716 | 348 |
| cast insertion | **67** | 192 | 95 | 300 | 125 |
| CC: enclose | 41 | 100 | **33** | 161 | 38 |
| CC: optimize | 89 | 121 | **60** | 228 | 63 |
| CC: concretize | 67 | 115 | **42** | 155 | 69 |
| CC: delay | 552 | 99 | **35** | 142 | 801 |
| CC: globalize | 118 | 219 | 183 | 221 | **105** |
| rco | 128 | 149 | **85** | 167 | 128 |
| lift locals | 44 | 55 | **27** | 205 | 50 |
| explicate control | 71 | 106 | 72 | 106 | **68** |
| select instructions | 134 | 111 | **52** | 111 | 222 |
| composition | 28 | 32 | 33 | **27** | 44 |
| shared modules not used by all four proofs | — | **15** | **15** | **15** | — |
| the graph model's meaning of the primitives | — | — | — | — | 34 |
| **total** | 2131 | 2582 | **1814** | 3620 | 2613 |

How to read the rows:
* **Semantics of the languages.** The graph model: ISWIM and the primitives (73, the same as the untyped pipeline's), and the typed languages, X86ᵀ among them (377: 66 for X86ᵀ; the lemmas, monotonicity, consistency and continuity, come from the infrastructure for intrinsically typed syntax, and X86ᵀ's select proof needs none). CEK: the ISWIM machine (74, as in the untyped pipeline), the framework instances (3), and the eight typed machines (597; X86ᵀ's 114). Interpreter: ISWIM and the clock (57) and the typed interpreters with their values and value relation (385; X86ᵀ's 110). Reduction: ISWIM's reduction semantics (48), those of ISWIMᵀ–Clos5ᵀ with their values (727: 458 for the reductions, 269 for the values), and the machines of Clos5ᵀ, Impᵀ, CFGᵀ and X86ᵀ it shares with the CEK column (288). Graph model with errors: ISWIM and the primitives (62) and the typed languages (456; X86ᵀ's 66).
* **Lemmas shared by the passes** (CEK only): two machines that both stop with the same observation or both step to related states (`Lock`, in `Common`, 9, used by the closure-conversion passes), and the Clos5ᵀ machine on atoms (`Clos5Common`, 11, used by rco and lift locals). The typed machines collect a tuple's values newest first in a vector, whose length gives the tuple's type by a reverse-append index (`m +ʳ j`, `vs <>< []`, `Framework/VecUtil.agda`), as ISWIMμ's machines do, so no proof needs the length equations of the tuples collected so far (since PR #67).
* **Simplify** is the untyped pipeline's proof in every column (the source language did not change), with the syntactic lemmas all of them use (`proof/Compiler/SimplifyFacts.agda`, 110 lines).
* **Cast insertion** is new; the untyped pipeline has no pass that inserts the checks (see [[#Typed against untyped]]). The CEK proof (192) includes 48 lines of list and primitive lemmas copied from adequacy, so that it does not import adequacy.
* **Select instructions** is CFGᵀ → X86ᵀ, an equation (≃) in both graph models, a forward simulation in the CEK and reduction columns (the same proof), clock for clock with equal results in the interpreter. X86ᵀ holds the values of Clos5ᵀ in CFGᵀ's frame, so no proof relates values or frames; its only check is `project`'s (`chk`). See [[#Typed assembly language]].
* **Shared modules.** Cast insertion needs a closed program, so all four proofs use the scoping lemmas (`SimplifyScope`, `CastScope`), which are therefore not counted; the operational proofs count only the observations (15). See [[#Shared modules]].

Language-independent infrastructure, not in any total (see [[#Language-independent infrastructure]]); each proof column is the part of a group that the proof reaches. The typed pipeline adds typed indices, lookup in typed lists and vectors (`Membership`, `Lookup`, `VecUtil`, `VecSelect`, `VecProj`), decidable base types (`PrimitivesDec`), the semantics of intrinsically typed syntax in the graph model (`GraphModel/Typed*`, which gives each typed semantics its monotonicity, consistency and continuity from per-operator facts), simulations in which both machines move (`Both`), kits for renaming and substitution and operands in vectors for the reduction semantics (`Syntax/Kit`, `ReductionVec`), and `ws?` (`Syntax/ScopeDec`). X86ᵀ added none:

| language-independent infrastructure (not in the totals) | lines | used by denotational: graph model | used by CEK machine + simulation | used by clocked interpreter + value relations | used by reduction semantics + simulation | used by graph model with errors |
|---|---:|---:|---:|---:|---:|---:|
| abstract binding trees | 190 | 190 | 190 | 190 | 190 | 190 |
| syntax lemmas (renaming, scoping, uses, substitution), list lookups | 519 | 418 | 418 | 418 | 504 | 418 |
| base types, logical equivalence | 58 | 58 | 58 | 58 | 58 | 58 |
| typed indices, lookup in typed lists, vectors (collecting, selecting, projecting) | 130 | 98 | 110 | 118 | 110 | 98 |
| denotational framework | 375 | 350 | — | — | — | 375 |
| graph model: values, consistency, machinery for any operators | 364 | 364 | — | — | — | 364 |
| graph model: its operators | 623 | 623 | — | — | — | 474 |
| graph model with errors: the error monad, its operators and laws | 935 | — | — | — | — | 935 |
| graph model: semantics of intrinsically typed syntax | 237 | 139 | — | — | — | 190 |
| small-step framework: transition systems, simulations | 273 | — | 273 | — | 273 | — |
| reduction framework: reduction semantics, simulations between them | 254 | — | — | — | 254 | — |
| clocked big-step framework | 249 | — | — | 249 | — | — |
| runs of a step function from any state | 29 | — | — | — | — | — |
| **total** | 4236 | 2240 | 1049 | 1033 | 1389 | 3102 |

Adequacy uses 2408 lines of the infrastructure, 168 of them not used by the denotational proof.

Adequacy relates the denotational semantics of ISWIM, Clos5ᵀ and X86ᵀ to their machines. It turns `CompilerCorrect`, and the end-to-end theorem for the whole compiler, `compile-x86`, into statements about running programs (`proof/Adequacy/EndToEnd.agda`, `proof/Adequacy/GraphErr/EndToEnd.agda`). It is reported separately, because the denotational semantics can be taken as *the* semantics of a language, in which case adequacy is not needed; its sizes are internal information, not part of the comparison. It is an add-on to the denotational proof, so its total also counts the shared modules it imports that the denotational total does not already count (the observations and `GlobalizeOlder`, that globalize refers only to older definitions); the denotational total plus the adequacy total is then standalone, except for the infrastructure and for the machines, which adequacy reuses from the simulation proof and which are not counted again. The ISWIM rows are the untyped pipeline's proofs, unchanged; Clos5 is the Clos5ᵀ machine's, and X86ᵀ the X86ᵀ machine's, both direct in the graph model. The last column is the adequacy of the graph model with errors (for ISWIM, Clos5ᵀ and X86ᵀ, on errors, constants, answers and divergence), counted the same way against its own proof: the shared modules it uses that the errors column does not count, and the graph model's modules it reuses (`Adequacy.Common`).

| adequacy (denotational side only) | graph model | graph model with errors |
|---|---:|---:|
| ISWIM | **653** | 790 |
| Clos5 | 715 | — |
| X86ᵀ | **679** | 1215 |
| well-formedness of compiled programs | 41 | — |
| end to end | **33** | 125 |
| simplify through the ISWIM machine | — | 30 |
| shared modules not used by all four proofs, nor by the proof of its model | **69** | **69** |
| the graph model's modules it uses | — | 52 |
| **total** | **2190** | 2281 |
| the CEK proof it derives Clos5ᵀ adequacy from (not in the total) | — | 2126 |

The CEK modules that adequacy with errors reaches only to derive Clos5ᵀ adequacy: `proof.Correctness.CEK.CastSim` (144), `proof.Correctness.CEK.CastSimLemmas` (48), `proof.Correctness.CEK.Clos5Common` (11), `proof.Correctness.CEK.Common` (9), `proof.Correctness.CEK.ConcretizeSim` (115), `proof.Correctness.CEK.DelaySim` (99), `proof.Correctness.CEK.EncloseSim` (100), `proof.Correctness.CEK.ExplicateSim` (106), `proof.Correctness.CEK.GlobalizeSim` (219), `proof.Correctness.CEK.LiftLocalsSim` (55), `proof.Correctness.CEK.OptimizeSim` (121), `proof.Correctness.CEK.PipelineSim` (32), `proof.Correctness.CEK.RCOSim` (149), `proof.Correctness.CEK.SelectSim` (111), `proof.Correctness.CEK.SimplifySim` (464), `proof.Semantics.CEK.Simulation` (1), `Semantics.CEK.Typed.CFG` (33), `Semantics.CEK.Typed.Clos2` (75), `Semantics.CEK.Typed.Clos3` (78), `Semantics.CEK.Typed.Clos4` (83), `Semantics.CEK.Typed.ISWIM` (73).

* **X86ᵀ adequacy is direct in both graph models** (internal information): soundness and a logical relation between the semantics of X86ᵀ and its CEK machine (`proof/Adequacy/X86*.agda`, 679 lines with 41 for the compiled programs' conditions; `proof/Adequacy/GraphErr/X86*.agda`, 1215 lines, with about 50 in its end to end for the compiled programs' conditions), against 1240 and 2085 for untyped X86 (now the untyped pipeline's alone). The relations follow the types: a register, slot or flag is related at the type the state type gives it, and the open closure agrees with its slot; values are related as the Clos5ᵀ machine's are (the graph model reuses its relation, `Clos5Values`, split from Clos5ᵀ adequacy). Adequacy holds for every X86ᵀ program; soundness needs a consistent table in which each definition's code depends only on the older definitions (the semantics gives each the older ones, as Clos5ᵀ's does), which the compiled programs satisfy (from `globalize-older` and the table lemmas of the graph-model proofs of rco, lift locals, explicate control and select). The end-to-end theorems for `compile-x86` come from ISWIM adequacy, `compile-x86-same` and X86ᵀ adequacy, and no longer from the CEK column. In the graph model with errors this also settles the pilot's open point: X86ᵀ's semantics writes registers non-strictly (only `callq` and `chk` strictly), and it is faithful to the machine (no change to it was needed).
* **The adequacy of the graph model with errors for Clos5ᵀ is derived, not standalone.** It follows from ISWIM adequacy, its `Same` result for `compile` and the CEK column's end-to-end simulation (`PipelineSim`): the ISWIM machine on M and the Clos5ᵀ machine on `compile M` agree on every outcome (`proof/Adequacy/GraphErr/EndToEnd.agda`; with `Agree`, the end-to-end row). So its Clos5 row is —, and the CEK proof it relies on (the modules above) is shown in its own row, not in its total. A direct proof, a logical relation for Clos5ᵀ with errors as the untyped pipeline has for Clos5 (904 lines), would be about 1000 lines; keeping it derived is a choice made for now, and the comparison of the adequacy totals is not like for like.

Infrastructure reached by each graph model, and what adequacy adds:

| infrastructure group | lines | graph model | graph model with errors | both | adequacy adds: graph model | adequacy adds: graph model with errors |
|---|---:|---:|---:|---:|---:|---:|
| abstract binding trees | 190 | 190 | 190 | 190 | — | — |
| syntax lemmas (renaming, scoping, uses, substitution), list lookups | 519 | 418 | 418 | 418 | — | — |
| base types, logical equivalence | 58 | 58 | 58 | 58 | — | — |
| typed indices, lookup in typed lists, vectors (collecting, selecting, projecting) | 130 | 98 | 98 | 98 | 12 | 12 |
| denotational framework | 375 | 350 | 375 | 350 | — | — |
| graph model: values, consistency, machinery for any operators | 364 | 364 | 364 | 364 | — | — |
| graph model: its operators | 623 | 623 | 474 | 474 | — | — |
| graph model with errors: the error monad, its operators and laws | 935 | — | 935 | — | — | — |
| graph model: semantics of intrinsically typed syntax | 237 | 139 | 190 | 92 | — | — |
| small-step framework: transition systems, simulations | 273 | — | — | — | 127 | 273 |
| runs of a step function from any state | 29 | — | — | — | 29 | 29 |
| **total** | 3733 | 2240 | 3102 | 2044 | 168 | 314 |

The graph model with errors reuses these modules of the graph model's operators: `Framework.GraphModel.Continuity` (135), `Framework.GraphModel.DomainUtil` (15), `Framework.GraphModel.Ops` (324).

The experiments (a direct backward simulation for delay, and the direct denotational semantics of Imp with lift locals and explicate control proved against it) are of the untyped pipeline: see [[#The untyped pipeline (preserved)]].

### Audit-surface counts (ISWIM)

The lines a reader must audit to trust each style's theorems (see [[#Audit surface]]), not in the totals: the shared part (languages, passes, syntax, base types, typed indices, observations), counted once in the first column, the semantics of each style, and its theorem statements. The machines of Clos5ᵀ, Impᵀ, CFGᵀ and X86ᵀ are read for both the CEK and the reduction statements, so they appear in both semantics rows. The statements of the graph model with errors include its adequacy and end-to-end theorems, so they also read the ISWIM, Clos5ᵀ and X86ᵀ machines.

| audit surface (not in the totals) | lines | read for denotational: graph model | read for CEK machine + simulation | read for clocked interpreter + value relations | read for reduction semantics + simulation | read for adequacy | read for graph model with errors |
|---|---:|---:|---:|---:|---:|---:|---:|
| languages, compiler passes, syntax, base types (shared) | 1241 | 1176 | 1209 | 1202 | 1241 | 1209 | 1209 |
| graph model: domain, operators, semantics of each language | 401 | 401 | — | — | — | 401 | 135 |
| simulation: small-step machines, transition systems | 707 | — | 707 | — | 324 | 365 | 365 |
| interpreter: clocked interpreters, results | 410 | — | — | 410 | — | — | — |
| reduction: reduction semantics, machines of the first-order languages, transition systems | 854 | — | 324 | — | 854 | 291 | 291 |
| graph model with errors: domain, error-propagating operators, semantics of each language | 863 | 135 | 365 | — | 291 | 500 | 863 |
| graph model: theorem statements | 72 | 72 | — | — | — | — | — |
| simulation: theorem statements | 48 | — | 48 | — | — | — | — |
| interpreter: theorem statements | 52 | — | — | 52 | — | — | — |
| reduction: theorem statements | 48 | — | — | — | 48 | — | — |
| adequacy: theorem statements | 49 | — | — | — | — | 49 | — |
| graph model with errors: theorem statements | 119 | — | — | — | — | — | 119 |
| **total** | 4040 | **1649** | 1964 | 1664 | 2143 | 2024 | 2191 |

The adequacy statements also use ρ₀ from the denotational ones (Theorems/Denotational.agda), not counted in its column.

### Shared modules (ISWIM)

| shared module | lines | used by |
|---|---:|---|
| `Compiler.Cast` | 31 | all four proofs |
| `Compiler.Concretize` | 36 | all four proofs |
| `Compiler.Delay` | 25 | all four proofs |
| `Compiler.EncloseScope` | 3 | all four proofs |
| `Compiler.Enclose` | 18 | all four proofs |
| `Compiler.Explicate` | 33 | all four proofs |
| `Compiler.Globalize` | 53 | all four proofs |
| `Compiler.LiftLocals` | 16 | all four proofs |
| `Compiler.Optimize` | 67 | all four proofs |
| `Compiler.Pipeline` | 13 | all four proofs |
| `Compiler.RCO` | 39 | all four proofs |
| `Compiler.Select` | 58 | all four proofs |
| `Compiler.Simplify` | 132 | all four proofs |
| `Language.ISWIM` | 26 | all four proofs |
| `Language.Prim` | 10 | all four proofs |
| `Language.Reg` | 3 | all four proofs |
| `Language.Typed.CFG` | 30 | all four proofs |
| `Language.Typed.Clos2` | 14 | all four proofs |
| `Language.Typed.Clos3` | 14 | all four proofs |
| `Language.Typed.Clos4` | 15 | all four proofs |
| `Language.Typed.Clos5` | 41 | all four proofs |
| `Language.Typed.ISWIM` | 14 | all four proofs |
| `Language.Typed.Imp` | 21 | all four proofs |
| `Language.Typed.Mon` | 49 | all four proofs |
| `Language.Typed.Type` | 44 | all four proofs |
| `Language.Typed.X86` | 98 | all four proofs |
| `Semantics.Observation` | 15 | simulation, interpreter, reduction, adequacy, adequacy with errors |
| `proof.Compiler.CastScope` | 17 | all four proofs |
| `proof.Compiler.GlobalizeOlder` | 54 | adequacy, adequacy with errors |
| `proof.Compiler.SimplifyScope` | 125 | all four proofs |

Shared by all four proofs, not counted: 28 modules, 1045 lines.
Counted in graph model: none.
Counted in simulation: `Semantics.Observation` (15).
Counted in interpreter: `Semantics.Observation` (15).
Counted in reduction: `Semantics.Observation` (15).
Counted in adequacy: `proof.Compiler.GlobalizeOlder` (54), `Semantics.Observation` (15).
Counted in graph model with errors: none.
Counted in adequacy with errors: `proof.Compiler.GlobalizeOlder` (54), `Semantics.Observation` (15).
Of the graph model, counted in graph model with errors: `Semantics.Graph.Prim` (+ proof/) (34).
Of the graph model, counted in adequacy with errors: `proof.Adequacy.Common` (52).
Examples, not counted: 119 lines.

### Infrastructure modules (ISWIM)

| infrastructure module | lines | used by |
|---|---:|---|
| `Framework.Clocked` (+ proof/) | 249 | interpreter |
| `Framework.GraphModel.DOpSig` (+ proof/) | 46 | graph model, adequacy, graph model with errors, adequacy with errors |
| `Framework.GraphModel.Domain` (+ proof/) | 70 | graph model, adequacy, graph model with errors, adequacy with errors |
| `Framework.GraphModel.Env` (+ proof/) | 84 | graph model, adequacy, graph model with errors, adequacy with errors |
| `Framework.GraphModel.ErrorMonad` (+ proof/) | 935 | graph model with errors, adequacy with errors |
| `Framework.GraphModel.OpsBase` (+ proof/) | 36 | graph model, adequacy, graph model with errors, adequacy with errors |
| `Framework.GraphModel.Ops` (+ proof/) | 324 | graph model, adequacy, graph model with errors, adequacy with errors |
| `Framework.GraphModel.SetsAsPredicates` (+ proof/) | 56 | graph model, adequacy, graph model with errors, adequacy with errors |
| `Framework.GraphModel.TypedCheck` | 3 | graph model with errors, adequacy with errors |
| `Framework.GraphModel.TypedGuard` (+ proof/) | 13 | graph model, adequacy |
| `Framework.Iff` | 3 | graph model, simulation, interpreter, reduction, adequacy, graph model with errors, adequacy with errors |
| `Framework.ListUtil` (+ proof/) | 114 | graph model, simulation, interpreter, reduction, adequacy, graph model with errors, adequacy with errors |
| `Framework.Lookup` (+ proof/) | 37 | graph model, simulation, interpreter, reduction, adequacy, graph model with errors, adequacy with errors |
| `Framework.Membership` | 20 | graph model, simulation, interpreter, reduction, adequacy, graph model with errors, adequacy with errors |
| `Framework.PrimitivesDec` | 38 | graph model, simulation, interpreter, reduction, adequacy, graph model with errors, adequacy with errors |
| `Framework.Primitives` | 17 | graph model, simulation, interpreter, reduction, adequacy, graph model with errors, adequacy with errors |
| `Framework.ReductionVec` (+ proof/) | 19 | reduction |
| `Framework.Reduction` (+ proof/) | 235 | reduction |
| `Framework.Smallstep` (+ proof/) | 127 | simulation, reduction, adequacy, adequacy with errors |
| `Framework.Syntax.Kit` | 9 | reduction |
| `Framework.Syntax.Rename` (+ proof/) | 59 | graph model, simulation, interpreter, reduction, adequacy, graph model with errors, adequacy with errors |
| `Framework.Syntax.ScopeDec` | 11 | graph model, simulation, interpreter, reduction, adequacy, graph model with errors, adequacy with errors |
| `Framework.Syntax.Scope` (+ proof/) | 32 | graph model, simulation, interpreter, reduction, adequacy, graph model with errors, adequacy with errors |
| `Framework.Syntax.SigUtil` | 4 | graph model, simulation, interpreter, reduction, adequacy, graph model with errors, adequacy with errors |
| `Framework.Syntax.Subst` (+ proof/) | 139 | graph model, simulation, interpreter, reduction, adequacy, graph model with errors, adequacy with errors |
| `Framework.Syntax.SyntaxUtil` | 6 | graph model, simulation, interpreter, reduction, adequacy, graph model with errors, adequacy with errors |
| `Framework.Syntax.Uses` (+ proof/) | 44 | graph model, simulation, interpreter, reduction, adequacy, graph model with errors, adequacy with errors |
| `Framework.VecSelect` (+ proof/) | 41 | graph model, simulation, interpreter, reduction, adequacy, graph model with errors, adequacy with errors |
| `Framework.VecUtil` (+ proof/) | 12 | simulation, reduction, adequacy, adequacy with errors |
| `Framework.abt.AbstractBindingTree` | 14 | graph model, simulation, interpreter, reduction, adequacy, graph model with errors, adequacy with errors |
| `Framework.abt.Fold2` | 19 | graph model, adequacy, graph model with errors, adequacy with errors |
| `Framework.abt.GSubst` | 7 | graph model, simulation, interpreter, reduction, adequacy, graph model with errors, adequacy with errors |
| `Framework.abt.ScopedTuple` (+ proof/) | 129 | graph model, simulation, interpreter, reduction, adequacy, graph model with errors, adequacy with errors |
| `Framework.abt.Sig` | 16 | graph model, simulation, interpreter, reduction, adequacy, graph model with errors, adequacy with errors |
| `Framework.abt.Var` | 14 | graph model, simulation, interpreter, reduction, adequacy, graph model with errors, adequacy with errors |
| `proof.Framework.Both` | 30 | simulation, reduction, adequacy with errors |
| `proof.Framework.GraphModel.ContinuityBase` | 99 | graph model, adequacy, graph model with errors, adequacy with errors |
| `proof.Framework.GraphModel.Continuity` | 135 | graph model, adequacy, graph model with errors, adequacy with errors |
| `proof.Framework.GraphModel.DenotProperties` | 14 | graph model, adequacy, graph model with errors, adequacy with errors |
| `proof.Framework.GraphModel.DomainUtilBase` | 71 | graph model, adequacy, graph model with errors, adequacy with errors |
| `proof.Framework.GraphModel.DomainUtil` | 15 | graph model, adequacy, graph model with errors, adequacy with errors |
| `proof.Framework.GraphModel.Laws` | 83 | graph model, adequacy |
| `proof.Framework.GraphModel.RenameSem` | 49 | graph model, adequacy, graph model with errors, adequacy with errors |
| `proof.Framework.GraphModel.SemanticsCore` | 88 | graph model, adequacy, graph model with errors, adequacy with errors |
| `proof.Framework.GraphModel.SemanticsUses` | 25 | graph model with errors, adequacy with errors |
| `proof.Framework.GraphModel.SemanticsUtil` | 15 | graph model, adequacy |
| `proof.Framework.GraphModel.Semantics` | 82 | graph model, adequacy, graph model with errors, adequacy with errors |
| `proof.Framework.GraphModel.Strict` | 51 | graph model, adequacy |
| `proof.Framework.GraphModel.TypedBinders` | 39 | graph model with errors, adequacy with errors |
| `proof.Framework.GraphModel.TypedGraph` | 34 | graph model, adequacy |
| `proof.Framework.GraphModel.TypedOkBase` | 92 | graph model, adequacy, graph model with errors, adequacy with errors |
| `proof.Framework.GraphModel.TypedOk` | 56 | graph model with errors, adequacy with errors |
| `proof.Framework.Runs` | 29 | adequacy, adequacy with errors |
| `proof.Framework.Simulation` | 116 | simulation, reduction, adequacy with errors |
| `proof.Framework.Syntax.EnvRel` | 15 | no proof |
| `proof.Framework.Syntax.ScopeRename` | 19 | graph model, simulation, interpreter, reduction, adequacy, graph model with errors, adequacy with errors |
| `proof.Framework.Syntax.ScopeSubst` | 42 | reduction |
| `proof.Framework.Syntax.SubstRel` | 35 | reduction |
| `proof.Framework.VecProj` | 20 | interpreter |

Module (+ proof/): the definitions are on the audit surface, the lemmas in its proof/ half; the lines are those of both.

### Assurance

Not in any total, nor in the comparison: what checks that X86ᵀ is faithful to untyped X86, the target of the untyped pipeline (`Theorems/X86Erasure.agda`; loc.py's group "assurance (not in the totals)").

| assurance (not in the totals) | lines |
|---|---:|
| erasure: select emits the instructions of select into untyped X86 | 164 |
| erasure keeps the meaning of every X86ᵀ program (CEK machines) | 395 |
| the statements (`Theorems/X86Erasure.agda`) | 14 |

* **Erasing X86ᵀ to X86 keeps the meaning of every well-typed X86ᵀ program.** This is proved once, in the CEK machines (`Theorems/X86Erasure.agda`, `erase-correct` and `erase-errors`; proof `proof/Assurance/X86Erasure.agda`, 324 lines, with 71 lines of `proof/Assurance/X86Agree.agda` kept from the proof of select into untyped X86), as a simulation of the X86ᵀ machine by the untyped X86 machine. An X86 value is the erasure of a typed one, and the X86 frame agrees on the typed slots and has the body's n slots. A register or flag that X86ᵀ treats as unset is unconstrained. While a closure is open, its X86 slot holds the code and environment X86ᵀ recorded. Each X86ᵀ instruction is matched by its erased ones, and `chk`'s erased test errs exactly when `chk` fails. So the machines are Equivalent, and the erased program reaches none of X86's other trapped errors.
* **Select emits the instructions of select into untyped X86.** Without the types, the X86ᵀ code of `select P` is the X86 code of the typed pipeline's select before X86ᵀ (`select-erase : erase (select P) ≡ SelectX86.select P`), a syntactic check: the erasure (`Language/Typed/X86Erase.agda`, 41), select into X86 (`Compiler/SelectX86.agda`, 55) and the proof (`proof/Compiler/SelectErase.agda`, 68). The registers (`Language/Reg.agda`) are shared by X86ᵀ and X86.

### Typed against untyped

The typed pipeline against the preserved untyped one, column by column (from `loc.py --iswim`; the untyped columns are those of `loc.py --untyped`). In each column the lower of the two is bold.

| typed against untyped | denotational: graph model: untyped | denotational: graph model: typed | CEK machine + simulation: untyped | CEK machine + simulation: typed | clocked interpreter + value relations: untyped | clocked interpreter + value relations: typed | reduction semantics + simulation: untyped | reduction semantics + simulation: typed | graph model with errors: untyped | graph model with errors: typed |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| semantics of the languages | 492 | **450** | **655** | 674 | 467 | **442** | **639** | 1066 | **448** | 518 |
| lemmas shared by the passes | — | — | — | 20 | — | — | — | — | — | — |
| simplify | **342** | **342** | **574** | **574** | **640** | **640** | **716** | **716** | **348** | **348** |
| cast insertion | — | 67 | — | 192 | — | 95 | — | 300 | — | 125 |
| CC: enclose | 81 | **41** | 188 | **100** | 140 | **33** | 186 | **161** | 90 | **38** |
| CC: optimize | 134 | **89** | 224 | **121** | 170 | **60** | **222** | 228 | 149 | **63** |
| CC: concretize | 141 | **67** | 182 | **115** | 127 | **42** | 157 | **155** | 134 | **69** |
| CC: delay | 594 | **552** | 134 | **99** | 90 | **35** | 183 | **142** | 898 | **801** |
| CC: globalize | 155 | **118** | **157** | 219 | **111** | 183 | **192** | 221 | 157 | **105** |
| rco | **118** | 128 | 396 | **149** | 245 | **85** | 247 | **167** | 194 | **128** |
| lift locals | 142 | **44** | 172 | **55** | 98 | **27** | 306 | **205** | 138 | **50** |
| explicate control | 154 | **71** | 124 | **106** | 118 | **72** | 124 | **106** | 144 | **68** |
| select instructions | 224 | **134** | 235 | **111** | 107 | **52** | 235 | **111** | 363 | **222** |
| composition | 32 | **28** | **26** | 32 | **22** | 33 | **27** | **27** | **33** | 44 |
| shared modules not used by all four proofs | — | — | 456 | **15** | 456 | **15** | 456 | **15** | 398 | — |
| the graph model's meaning of the primitives | — | — | — | — | — | — | — | — | **34** | **34** |
| **total** | 2609 | **2131** | 3523 | **2582** | 2791 | **1814** | 3690 | **3620** | 3528 | **2613** |
| **total without cast insertion** | 2609 | **2064** | 3523 | **2390** | 2791 | **1719** | 3690 | **3320** | 3528 | **2488** |

| adequacy, typed against untyped | graph model: untyped | graph model: typed | graph model with errors: untyped | graph model with errors: typed |
|---|---:|---:|---:|---:|
| **total** | 3234 | **2190** | 4338 | **2281** |

* **Like for like.** The untyped pipeline has no pass that inserts the checks: every semantics down to X86 checks kinds itself, and a compiler to real x86 would still need a check-insertion pass somewhere (near select, as *Essentials of Compilation*'s tag bits are). So the row to compare is the total without cast insertion. Like for like, the typed pipeline is smaller in every column: the graph model by 21% (2609 → 2064), the CEK proof by 32% (3523 → 2390), the interpreter by 38% (2791 → 1719), the reduction proof by 10% (3690 → 3320) and the graph model with errors by 29% (3528 → 2488). Counting cast insertion: 2131, 2582, 1814, 3620 and 2613. The two pipelines' targets differ: the untyped one ends at untyped X86, the typed one at X86ᵀ, which erases to it (see [[#Assurance]]).
* **The effect of typing differs a lot by style.** The closure-conversion passes enclose to delay shrink, most in the interpreter (enclose 140 → 33, delay 90 → 35) and least in the reduction column (enclose 186 → 161, concretize 157 → 155; optimize even grows, 222 → 228): a reduction semantics substitutes values into typed terms, so its proofs keep the renaming and substitution lemmas, now at every type. Cast insertion costs the most there (300 lines, against 67 to 192), and its semantics row grows the most (639 → 1066: typed reductions and values for five languages, and the typed machines of Clos5ᵀ, Impᵀ, CFGᵀ and X86ᵀ that it shares with the CEK column). The reduction column gains least: 370 lines like for like.
* **Lift locals is nearly the identity, and select is small.** Impᵀ's frame is typed by the context of the Monᵀ term, so lift locals keeps the variables as they are (44, 55, 27 and 50 lines, against 98 to 172; reduction 306 → 205, which still relates a reduction semantics by substitution to the frames of the Impᵀ machine). The slots of the frame are typed indices down to X86ᵀ, whose frame is CFGᵀ's, so select, which grew in every column when it had to assign levels and show frames large enough for untyped X86 (`SelectFacts`), is now smaller than the untyped pipeline's everywhere: graph model 224 → 133, CEK and reduction 235 → 111, interpreter 107 → 52, graph model with errors 363 → 222.
* **Globalize grows in the operational columns** (CEK 157 → 219, interpreter 111 → 183, reduction 192 → 221): the pass makes each term over the table of definitions built so far, typed by it, and the proofs must weaken it to the final table (`⊢-wk`, `Faithful` in `GlobalizeSim`). It shrinks in the two graph models (155 → 118, 157 → 105).
* **Rco shrinks** in the operational columns (CEK 396 → 149, interpreter 245 → 85, reduction 247 → 167): there is no late code check to preserve, Monᵀ is monadic by construction, and typed terms are well scoped by construction, so the operational proofs no longer need `Scoped` and its 229 lines (`PipelineScope`), which leave the shared row (456 → 15; the closedness lemmas that cast insertion needs are used by all four typed proofs, and so not counted).
* **Delay in the graph model** shrinks least (594 → 552; with errors 898 → 801): the relation still cannot be indexed by the recursive type `Any`; see [[#Typed intermediate languages (pilot, superseded)|Typed intermediate languages (pilot)]].
* **The graph model with errors** was the one column that grew like for like (3529 → 3651) while the typed pipeline ended at untyped X86: select had to relate CFGᵀ, which checks only at `project`, to X86, which checks every operand (1349 lines, `Same`). Ending at X86ᵀ, select is ≃ (222) and the column is 29% smaller than the untyped one.
* **Adequacy** (internal information): the graph model's 3234 → 2190; the graph model with errors' 4338 → 2281, but its Clos5ᵀ adequacy is derived from the CEK column (above), so that comparison is not like for like. X86ᵀ adequacy is direct in both (679 and 1215, against untyped X86's 1240 and 2085).
* **The audit surface grows** in every style (graph model 1510 → 1649, CEK 1805 → 1964, interpreter 1619 → 1664, reduction 1729 → 2143, graph model with errors 1985 → 2191): the typed languages and semantics are larger to read than the untyped ones (X86ᵀ is 98 lines against X86's 48, and its semantics in each style is about the size of X86's), and the reduction column reads typed reductions and the typed machines it shares. The graph model's audit surface is now the smallest.

### The untyped pipeline (preserved)

The untyped pipeline, as it was before the typed port, preserved in `agda/Untyped/` (from `loc.py --untyped`). Since PR #58 it alone has untyped X86's semantics in the graph models and the interpreter, and its adequacy (moved to `agda/Untyped/`), with its totals unchanged; its audit surface reads the registers' module (`Language/Reg.agda`), one more module line. Its numbers differ from those of PR #53 by a few lines: the modules that both pipelines now use (the frames and tables of X86's semantics, `Semantics/Graph/Frames.agda` and `Semantics/GraphErr/Frames.agda`; the values of the X86 interpreter, `Semantics/Interp/Values.agda`; `block-at` in `Language/X86.agda`; ISWIM adequacy without the untyped compiler's corollaries, now `Untyped/proof/Adequacy/ISWIMCompile.agda`) were split off from the untyped modules, which adds or moves a module line or a definition (graph model 2608 → 2610, CEK 3526 → 3521, interpreter 2794 → 2795, reduction 3689 → 3684, graph model with errors 3528 → 3529; adequacy 3233 → 3234 and 4333 → 4338, with the values of the X86 machine now in the X86 row). The lemmas about X86's case that the two select proofs of the graph model shared word for word moved to the proof half of the X86 semantics (`proof/Semantics/Graph/X86.agda`, shared): the untyped graph model's select 271 → 224, its semantics 444 → 492. Its full tables, as those above, are printed by `loc.py --untyped`.

| component (untyped pipeline) | denotational: graph model | CEK machine + simulation | clocked interpreter + value relations | reduction semantics + simulation | graph model with errors |
|---|---:|---:|---:|---:|---:|
| semantics of the languages | 492 | 655 | 467 | 639 | **448** |
| simplify | **342** | 574 | 640 | 716 | 348 |
| CC: enclose | **81** | 188 | 140 | 186 | 90 |
| CC: optimize | **134** | 224 | 170 | 222 | 149 |
| CC: concretize | 141 | 182 | **127** | 157 | 134 |
| CC: delay | 594 | 134 | **90** | 183 | 898 |
| CC: globalize | 155 | 157 | **111** | 192 | 157 |
| rco | **118** | 396 | 245 | 247 | 194 |
| lift locals | 142 | 172 | **98** | 306 | 138 |
| explicate control | 154 | 124 | **118** | 124 | 144 |
| select instructions | 224 | 235 | **107** | 235 | 363 |
| composition | 32 | 26 | **22** | 27 | 33 |
| shared modules not used by all four proofs | — | 456 | 456 | 456 | **398** |
| the graph model's meaning of the primitives | — | — | — | — | 34 |
| **total** | **2609** | 3523 | 2791 | 3690 | 3528 |

| adequacy (untyped pipeline) (denotational side only) | graph model | graph model with errors |
|---|---:|---:|
| ISWIM | **653** | 790 |
| Clos5 | **587** | 904 |
| X86 | **1240** | 2085 |
| well-formedness of compiled programs | **262** | 376 |
| end to end | **36** | 43 |
| simplify through the ISWIM machine | — | 30 |
| shared modules not used by all four proofs, nor by the proof of its model | 456 | **58** |
| the graph model's modules it uses | — | 52 |
| **total** | **3234** | 4338 |

| experiment (untyped pipeline) (not in the totals) | lines |
|---|---:|
| simulation: direct backward simulation for delay — framework | 86 |
| simulation: direct backward simulation for delay — delay | 126 |
| graph model: direct Imp — semantics | 27 |
| graph model: direct Imp — lift locals | 78 |
| graph model: direct Imp — explicate control | 522 |

## What the groups contain

ISWIMμ (`agda/Mu/`, the groups `mu-*` of `loc.py`):

* **shared** (`mu-shared`; counted only in the proofs that use it when not all four do): the languages (`Mu/Language/`: the types `Type.agda`, ISWIMμ with its renaming and substitution `ISWIMSubst.agda`, Clos2μ–Clos5μ, Monμ, Impμ, CFGμ and X86μ), the passes (`Mu/Compiler/`) and their compositions (`Mu/Compiler/Pipeline.agda`), and `Mu/proof/Compiler/GlobalizeOlder.agda` (globalize refers only to older definitions, used by adequacy); also the ISWIM pipeline's registers, primitives and observations, which ISWIMμ uses.
* **language-independent infrastructure (not counted):** that of `agda/Framework/` (below), and ISWIMμ's own (`mu-infra`, `mu-rinfra`): heterogeneous vectors (`Mu/Framework/AllUtil.agda`, `Mu/proof/Framework/AllProp.agda`) and the reduction of their operands (`Mu/Framework/ReductionAll.agda` and its `proof/` half).
* **semantics of the languages** (`mu-den`, `mu-op`, `mu-ck`, `mu-red`): `Mu/Semantics/<style>/` with their lemmas in `Mu/proof/Semantics/<style>/`; the machines of Clos5μ, Impμ, CFGμ and X86μ are the CEK column's and the reduction column's (`mu-op+mu-red`, counted in both); the ISWIM pipeline's modules a column reuses (the graph model's meaning of the primitives, `Semantics/Graph/Prim.agda`; the instances of the frameworks at this compiler's observations) are counted in its total, in their own row.
* **one row per pass, composition:** as below, in `Mu/proof/Correctness/<style>/`; explicate control and select instructions are the CEK proofs in the reduction column too (`mu-op+mu-red`); simplify's syntactic lemmas (`Mu/proof/Compiler/SimplifyFacts.agda`) are in the simplify row of every column.
* **adequacy** (`mu-adeq`, reported separately): `Mu/proof/Adequacy/` but `CEK/`, for the clocked interpreters; **its alternative for the CEK machines** (`mu-adeq-cek`, in no total, shown beside it): `Mu/proof/Adequacy/CEK/`, with the tuples of sets, `Clos5Common` and `X86Compiled` in both (`mu-adeq+mu-adeq-cek`); **mixing semantics** (`mu-mix`, in no total): `Mu/proof/Mixed/CompilerMixed.agda`, whose bridge is adequacy's ISWIM row; **the no-error lemmas** (`mu-noerr`, in no total): `Mu/proof/Semantics/{CEK,Interp,Reduction}/NoError.agda`; **examples** (`mu-examples`, not counted): `Mu/proof/Compiler/Examples/`; **the theorem statements** (`mu-thm`, not counted; in the audit-surface table): `Mu/Theorems/`.

`loc.py` checks that ISWIMμ's columns use neither each other, nor adequacy, the no-error lemmas or the examples, nor a proof of either ISWIM pipeline (what the ISWIM pipelines share they may use).

The ISWIM pipeline (`agda/`), by the same rules:

* **shared (counted only in the proofs that use it when not all four do, see above):** the languages (untyped ISWIM, the typed languages in `Language/Typed/` with their types `Language/Typed/Type.agda`, X86ᵀ among them, its registers `Language/Reg.agda`, and the primitives `Language/Prim.agda`), the compiler passes (`Compiler/`) and their compositions `compile₄`, `compile`, `compile-mon`, `compile-imp`, `compile-cfg` and `compile-x86` (`Compiler/Pipeline.agda`), which all four proofs use; the observations and the end-theorem shape (`Semantics/Observation.agda`); and the lemmas about the compiler's output that the proofs use:
  * `Compiler/EncloseScope.agda` (closed ISWIM programs, `Closed`), `proof/Compiler/SimplifyScope.agda` (simplify keeps programs closed) and `proof/Compiler/CastScope.agda` (`simplify-ws`, `cast-closed-≡`): cast insertion needs a closed program;
  * `proof/Compiler/GlobalizeOlder.agda`: globalize refers only to older definitions (used by adequacy).
* **language-independent infrastructure (not counted):** see [[#Language-independent infrastructure]].
  * the abt library (`Framework/abt/`), `Framework/Syntax/SigUtil`, `Framework/Syntax/SyntaxUtil`;
  * `Framework/Syntax/` (lemmas in `proof/Framework/Syntax/`): the syntax of any signature and the lemmas about it (renaming, scoping and `ws?`, uses, substitution, kits for renaming and substitution of typed terms), and `ListUtil.agda`, lookups in lists;
  * `Framework/Primitives.agda` (base types), `Framework/PrimitivesDec.agda` (their decidable equality) and `Framework/Iff.agda` (`_⇔_`);
  * typed indices and suffixes (`Membership`), lookup in typed lists (`Lookup`), and vectors: collecting, selecting the kept positions, projecting from tuples of a size (`VecUtil`, `VecSelect`, `VecProj`);
  * the denotational framework: sets as predicates, environments, DOp signatures, `abt.Fold2`, and in `proof/Framework/GraphModel/` the semantics of any signature and its monotonicity, monotonicity and consistency of operators (`DenotProperties`), `RenameSem`;
  * the graph model, `Framework/GraphModel/`, in four groups: (a) values and consistency (`Domain`), the operators the two models share unchanged (`OpsBase`), the machinery for any operators (`ContinuityBase`), the properties of whole terms of any graph-model semantics (`SemanticsCore`) and facts about values (`DomainUtilBase`); (b) the graph model's operators (`Ops`), their continuity (`Continuity`), their β laws on terms (`SemanticsUtil`), facts about them (`DomainUtil`), operators strict in their operands (`Strict`) and the let/case and strict-write laws (`Laws`); (c) the error monad of the graph model with errors, its operators and their laws (`ErrorMonad`); (d) the semantics of intrinsically typed syntax (`Typed*`: `Ok`, monotone, consistent and continuous, and its combinators for an operator, a variable, a constant, a let, a vector of operands, code and binders; the guard of `project` and its check in the errors model);
  * the small-step framework (`Framework/Smallstep.agda`; `proof/Framework/{Smallstep,Simulation,Both}.agda`: lemmas about runs, forward simulation, backward from forward plus determinism, simulations in which both machines move) and the clocked one (`Framework/Clocked.agda`), both parameterized over the type of observations;
  * the reduction framework (`Framework/Reduction.agda`, `Framework/ReductionVec.agda`: reductions as step functions with congruence rules, operands in vectors), and the substitution library (`Framework/Syntax/Subst.agda`, `proof/Framework/Syntax/{Subst,ScopeSubst,SubstRel}.agda`), used only by the reduction proof.
* **semantics of the languages:**
  * denotational: the meaning of this compiler's primitives (`Semantics/Graph/Prim.agda`: `out`, `primD` and its lemmas), the semantics of ISWIM, and those of the typed languages, X86ᵀ among them (`Semantics/Graph/Typed/`, with the guard of `project`, `Ops`), with their lemmas in `proof/Semantics/Graph/` (for ISWIM, the continuity simplify's proof uses);
  * Simulation: the ISWIM machine, the machines of the typed languages, X86ᵀ among them (`Semantics/CEK/Typed/`), and the small-step framework at this compiler's observations (`Semantics/CEK/Smallstep.agda`, `proof/Semantics/CEK/Simulation.agda`);
  * Interpreter: the ISWIM interpreter, the typed interpreters, X86ᵀ's among them, with their values and the value relation (`Semantics/Interp/Typed/`, `proof/Semantics/Interp/Typed/`), and the clocked framework at this compiler's observations (`Semantics/Interp/Clock.agda`);
  * Reduction: the reduction semantics of ISWIM and of ISWIMᵀ–Clos5ᵀ (`Semantics/Reduction/`, `Semantics/Reduction/Typed/`), with their values in their proof/ halves, the framework instance (`Semantics/Reduction/Smallstep.agda`), and the machines of Clos5ᵀ, Impᵀ, CFGᵀ and X86ᵀ, which are the CEK column's and are counted in both.
* **one row per pass:** that pass's correctness proof. Each row with a composition also contains the end-to-end theorem for the prefix of the compiler it ends (`compile-mon`, `compile-imp`, `compile-cfg`, `compile-x86`) where its proof states it.
* **composition:** the end-to-end theorem built from the per-pass results (`PipelineSim`, `PipelineRed`, `CompilerFuel`, `CompilerCorrect`).
* **shared modules not used by all four proofs:** see [[#Shared modules]].
* **simplify:** the pass (`Compiler/Simplify.agda`) is shared, as every pass is; its syntactic lemmas (`proof/Compiler/SimplifyFacts.agda`), which all its proofs use, are counted in the simplify row of every column. See [[#Simplify]].
* **the preserved untyped pipeline** (`agda/Untyped/`): its own groups, by the same rules; what it shares with the typed pipeline (ISWIM, simplify and its proofs, the primitives, the observations, the ISWIM adequacy) is counted in both. Untyped X86, its semantics in every style and its adequacy are the untyped pipeline's (X86 and its CEK machine stay in `agda/`, since the assurance uses them).
* **assurance (not in the totals):** what checks that X86ᵀ is faithful to untyped X86 (`Theorems/X86Erasure.agda`, `proof/Assurance/`, the erasure and select into untyped X86, `Compiler/SelectX86.agda`, with its proof `proof/Compiler/SelectErase.agda`); see [[#Assurance]].

## Caveats

Some caveats are about the untyped pipeline only (marked so); the typed ISWIM pipeline's passes have no preconditions but the closedness of the source program, and ISWIMμ's have none (a program is a closed term of any type, by its type).

* **The theorems differ** (ISWIM pipeline). The simulation, interpreter and reduction theorems have the same shape. They are stronger than the denotational one: they separate errors from divergence. In the graph model, both denote ∅. In the graph model with errors every pass but delay is an equation. For ISWIMμ, which has no errors, the four columns state the same end-to-end theorem for `main : Int` (the graph model through adequacy; see [[#Current counts]]).
* **Terminology: "error".** An error (the observation `o-error`, the `error` result of an interpreter or of `red`) is a *trapped* error in the sense of Cardelli ("Type Systems"): the program stops and the semantics reports it. Every operational semantics here is a total step or eval function, so no program can get stuck, which would be an *untrapped* error; a term that `red` cannot reduce is reported as an error. (Before this, the code said "wrong", after Milner, which in Cardelli's terms usually means an untrapped error.) The graph model does not distinguish errors from divergence: both denote ∅. The graph model with errors, using ω, does, for the whole compiler; see [[#Graph model with errors]].
* **Determinism.** The simulation and reduction proofs rely on every machine and reduction being deterministic and total. The backward direction of each pass comes from forward simulation plus determinism, and the framework proves that once. The interpreter proof needs no determinism argument: an interpreter is a function, and every pass but simplify is proved clock for clock (see below); simplify's clock-monotone proof uses the interpreter's monotonicity in the clock instead.
* **Why "backward = forward + determinism" has no denotational counterpart.** Consistency of denotations plays the role of determinism. Take c ∈ ⟦pass M⟧ and suppose ⟦M⟧ has an element.
  * If it is a constant c′, the forward direction puts c′ in ⟦pass M⟧, and consistency forces c = c′.
  * If it is a function, tuple or sum, consistency rules out c.

  That leaves ⟦M⟧ = ∅, and showing that ⟦pass M⟧ = ∅ too is a reflection argument. A forward relation cannot carry absence.

  This is inherent in a continuous semantics. Every element of a denotation is a finite observation, evidence available after finitely much computation. Termination with a result is a finite observation; divergence is not, since no finite evidence shows that a program diverges. So divergence can only appear as the absence of elements, and an element marking divergence would make the semantics non-monotone. The simulation proof avoids this because its divergence is an infinite run, a coinductive object that forward simulation maps to another infinite run.

  Adding an error element to the graph model would not change this. It would make an error a finite observation, handled by the forward direction plus consistency, but ∅ would still mean divergence and would still have to be reflected. Avoiding the reflection would take a coinductive semantics, such as the delay monad or traces, and that gives up the finite-observation style.

  The cost falls only on passes that change representation. When ⟦pass M⟧ ≃ ⟦M⟧ (enclose, optimize, concretize, globalize, rco, lift locals, explicate control), both directions come from the equation at once, with no determinism argument.
* **Machines.** In the typed pipeline only the ISWIM machine checks kinds; the typed machines check nothing but `project`, which cast insertion places where the ISWIM machine checks, and select compiles each `project` to X86ᵀ's `chk`, which stands for an X86 instruction that errs on a value of another kind. *Untyped pipeline:* the ISWIM, Clos2 and Clos3 machines check that an operator is a function before evaluating the argument. Delay needs this to preserve errors: it takes the closure apart with `fst` before the argument. The Clos4 and Clos5 machines check that the operator is code only at the call, after all three operands, like an indirect call instruction, so that rco, which let-binds all the operands before the call, preserves errors. On delay's output the late check always passes, since a non-closure has already stopped with an error at `fst`.

* **Binders bind only consistent sets.** In the graph model, Λ and 𝒞 bind only finite sets that are consistent, so a denotation under a consistent environment has no inconsistent elements. This was needed for explicate control: with binders that admit any finite set, ⟦explicate P⟧ ≃ ⟦P⟧ is false (see [[#Explicate control]]). It cost 96 denotational lines and 74 adequacy lines when it was made, and saved 16 in delay, whose own consistency induction gave way to a generic one: the monotonicity proof of the denotational framework now works for any relation the operators preserve, so the consistency of each semantics comes from its operator lemmas. Where a proof picks a finite part of a set for a binder (concretize, delay in both directions, rco's let-β), it needs that set consistent, so those proofs take a consistent environment.
* **Two denotational semantics of Imp** (untyped pipeline). The main rows use a continuation-passing semantics of Imp (`Semantics/Graph/ImpK.agda`); a direct one (`proof/Semantics/Graph/ImpDirect.agda`), with lift locals and explicate control proved against it, is kept as an experiment. Choosing the semantics is part of the proof effort, as choosing the machines or interpreters is for the operational styles; the CPS one is the better effort for this pass sequence. See [[#Explicate control]].
* **Clos5 continuity is denotational** (untyped pipeline). The continuity of the Clos5 semantics in the environment (117 lines then, 118 now), formerly adequacy's `Clos5Continuous`, is now `proof/Semantics/Graph/Clos5IswimContinuous.agda`, in the denotational row "semantics of the languages", because the rco proof uses it (for the let laws), as does lift locals. Adequacy reuses it from there and does not count it again; adequacy's Clos5 row shrank by the same 117 lines.
* **The rco preconditions differ** (untyped pipeline; the typed rco theorems have none, since typed terms are well scoped). The denotational rco theorem is an equation with no precondition on programs; the three operational ones (CEK, interpreter, reduction) need `Scoped`, and their end-to-end `compile-mon` theorems therefore pay for `compile-scoped` (249 lines, in the shared row, plus `Syntax/ScopeRename`, now infrastructure). See [[#Remove complex operands]].
* **The reduction proof's concretize needs a well-scoped program** (untyped pipeline; `WS 0`), which the CEK and interpreter proofs do not: a variable of a closure's code beyond its parameters becomes, in Clos2 and in Clos3, two different variables, which substitution then moves differently, while the machines look both up in the closure's environment, where both fail. The compiler's composition discharges it with `optimize-closed` (shared, `Compiler/PipelineScope`). See [[#Reduction semantics + simulation]].
* **The small-step framework answers a stop by a run.** A forward simulation now may answer a source that stops with a target run to a final state (`runs`, not only `stops`): a reduction target often has administrative steps left (a projection, a let, the evaluation of an atom) when the source errors or reaches a value. The end theorem still follows by determinism (`final-unique`, +9 lines of infrastructure); the CEK proofs do not use it.
* **Lift locals and explicate control need no precondition in any style.** A variable out of scope becomes a slot beyond the frame, which errors (operationally) or reads as `init` (denotationally) exactly where the Clos5 variable does. Assigning a slot beyond the frame errors in all four styles (∅ denotationally, since explicate control; see [[#Explicate control]]). See [[#Lift locals]].
* **Select instructions: a precondition only in the denotational proof** (untyped pipeline; in the typed one a frame is typed, so select's frames are large enough and no theorem has a precondition). The denotational theorem assumes every global definition has at least 2 locals (`select-correct`), discharged for compiled programs; neither operational one has a precondition. See [[#Select instructions]].
* **Adequacy reaches X86ᵀ, the final target, but not the intermediate languages.** Adequacy, and so a statement about running code, exists for ISWIM, Clos5ᵀ (Clos5 in the untyped pipeline) and X86ᵀ (X86 in the untyped pipeline); in the graph model with errors, Clos5ᵀ's is derived from the CEK column's simulation, X86ᵀ's is direct (see [[#Counts of the ISWIM pipeline]]): the end-to-end theorem for `compile-x86` relates the ISWIM machine to the X86ᵀ machine (`end-to-end-x86-const`, `end-to-end-x86-converges`, and with errors also on errors and divergence). The end-to-end denotational theorems for `compile-mon`, `compile-imp` and `compile-cfg` still speak only about the denotations of Monᵀ, Impᵀ and CFGᵀ. X86ᵀ soundness has preconditions that compiled programs satisfy (a consistent table, whose definitions refer only to older ones), discharged in the proofs; in the plain graph model, like Clos5's, it cannot tell an error from divergence.

## Audit surface

The development is split, as in jsiek/AI-for-pl, into what must be read to trust the results and what Agda has checked (see `agda/README.md`):

* **the theorem statements**: ISWIMμ's, `agda/Mu/Theorems/{Denotational,Simulation,Interpreter,Reduction,Adequacy}.agda` (each pass in each style, the compiler into Clos5μ, Monμ, Impμ, CFGμ and X86μ at any type, and the end-to-end theorem for `main : Int`, the operational styles' and, through adequacy, the graph model's; see [[#Current counts]]); the ISWIM pipeline's, `agda/Theorems/{Denotational,Simulation,Interpreter,Reduction,Adequacy,GraphErrors}.agda`, and the assurance's `agda/Theorems/X86Erasure.agda` (those of the untyped pipeline in `agda/Untyped/Theorems/`): each public theorem with its full type, defined as the theorem of `agda/proof/` (`enclose-correct = EncloseCorrect.enclose-correct-closed`), so Agda checks that the statement is the type of the proof;
* **the definitions they use**, everything else outside the `proof/` directories: for ISWIMμ, `agda/Mu/` outside `agda/Mu/proof/` (its languages, passes, semantics in each style, and heterogeneous vectors) and what it uses of `agda/` (the frameworks, the observations, the instances of the frameworks at them, the primitives); for the ISWIM pipeline, the languages and passes (`agda/Language/`, `agda/Language/Typed/`, `agda/Compiler/`), the semantics of each style (`agda/Semantics/Graph/`, `agda/Semantics/CEK/`, `agda/Semantics/Interp/`, `agda/Semantics/Reduction/`, `agda/Semantics/GraphErr/`, each with a `Typed/` directory for the typed languages, and `agda/Semantics/Observation.agda`), and the language-independent definitions in `agda/Framework/` (the abt extract, syntax and substitution, typed indices, the graph model's sets, values and operators and the error monad, the small-step, reduction and clocked frameworks); for the untyped pipeline, also those of `agda/Untyped/` outside `agda/Untyped/proof/`;
* **`agda/proof/`** (and `agda/Mu/proof/`, `agda/Untyped/proof/`), mirroring the paths of the surface: all proofs, and the lemmas of every module that mixed definitions and lemmas (`agda/X.agda` keeps the definitions, `agda/proof/X.agda` re-exports them with the lemmas).

`loc.py` checks that no module of the surface imports a proof module (the theorem files excepted) and that every module outside the `proof/` directories is reached from the theorem files of one of the ISWIM pipelines, or, for those of `agda/Mu/`, from ISWIMμ's, so each surface is exactly the closure of its statements, at the granularity of modules. (Making ISWIMμ's surface closed moved two modules: the lemmas about heterogeneous vectors, `AllProp`, to `Mu/proof/Framework/`, and the lemmas about the reduction of their operands, `Each`, `ans-∷`, `pairs`, to the new proof half of `Mu/Framework/ReductionAll.agda`, whose surface half keeps `red-∷`.) Two choices keep it small:

* **Restricted statements** (as written for the untyped pipeline; the typed one does the same with `globalize-older`, and for X86ᵀ with `X86Compiled` and, with errors, `compile-ok`). Adequacy for the Clos5 and X86 machines is proved for any well-formed program, but the well-formedness conditions (references only to older definitions, slots within the frame, a consistent table: `Clos5WF`, `X86WF` and `RB` of `GlobalizeCorrect`, about 60 lines) are proof-internal, so `Theorems/Adequacy.agda` states it for the programs the compiler produces (`compile M`, `compile-x86 M` for a closed `M`), discharging well-formedness with `compile-wf` and `compile-x86-wf`. Soundness and adequacy are stated as their characterizations (`const-iff`, `nonempty-iff`, `error-empty`, `diverges-empty`), so `ShapeOf` stays in `agda/proof/`. The denotational `select-correct` states its precondition inline (`All (λ b → 2 ≤ Body.locals b) (defs P)`), and `ρ₀` is defined in `Theorems/Denotational.agda` (the proofs use a definitionally equal one, in the graph model's `Domain`). ISWIMμ's statements are restricted the same way: X86μ adequacy is stated for `compile-x86 M` (`X86Compiled` discharges its conditions), the graph model's statements write `Same` out as its two conjuncts, and `ρ₀` is defined in `Mu/Theorems/Denotational.agda`.
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
| 2026-10-13 | `let` in ISWIM, Clos2 and Clos3 (semantics in every style, every pass, every proof); simplify emits `let x = M' in N'` where it left the redex `(λ x. N') M'`, and simplifies a source `let` like β (PR #43; see [[#Adding let to ISWIM, Clos2 and Clos3\|Adding let]]) | 3393 (+94) | 3639 (+58) | **2933** (+41) | 3904 (+94) |
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
| 2026-10-13 | typed intermediate languages, a pilot (ISWIM → Clos4; not in the totals): cast insertion into intrinsically typed ISWIMᵀ–Clos4ᵀ (closures in Clos4ᵀ packed as ∃ n. code n × tup n), typed enclose, concretize and delay, in the CEK and graph-with-errors columns; the CC passes shrink (CEK enclose 188 → 106, concretize 182 → 115, delay 134 → 101; graph model with errors enclose 90 → 38, concretize 134 → 69) but not delay in the graph model with errors (898 → 919), and cast insertion costs 195 / 122; the segment, without optimize, CEK 1032 → 1083, graph model with errors 1541 → 1741. New infrastructure 48 (3756 → 3804); see [[#Typed intermediate languages (pilot, superseded)\|Typed intermediate languages (pilot)]] | **2608** | 3526 | 2794 | 3689 |
| 2026-10-14 | typed pilot, step 2 (not in the totals): typed optimize on Clos2ᵀ in both columns (CEK 133 against 224, graph model with errors 63 against 149); infrastructure for semantics of intrinsically typed syntax (201 lines, the pilot's own infrastructure table), which takes the typed graph lemmas from 266 to 70 lines; Clos4ᵀ closures project as functions, delay in the graph model with errors 919 → 878. The segment, like for like without cast insertion: CEK 1062 against 1311, graph model with errors 1489 against 1745 | **2608** | 3526 | 2794 | 3689 |
| 2026-10-14 | the typed pipeline is the main one (PRs #55, #56): cast insertion into intrinsically typed ISWIMᵀ, Clos2ᵀ–Clos5ᵀ, Monᵀ, Impᵀ and CFGᵀ, every pass and the compiler proved in all five columns, adequacy for Clos5ᵀ and X86 in both graph models; the untyped pipeline preserved in `agda/Untyped/` (its totals, a few lines off by the modules the two now share: 2610, 3521, 2795, 3684; graph model with errors 3528 → 3529 untyped, 3776 typed). Like for like, without cast insertion: 2242, 2673, 1865, 3536; see [[#Typed against untyped]] | 2309 | 2868 | **1960** | 3836 |
| 2026-10-14 | typed assembly language, a pilot (not in the totals): X86ᵀ, intrinsically typed X86 (register, frame, flag and open-closure types; project's check `chk` its only trapped error), typed select CFGᵀ → X86ᵀ emitting today's instructions (proved), in the CEK column (select, `SelectFacts` and the target's machine 482 → 228) and the graph model with errors (select ≃ instead of `Same`; 1489 → 291); the language and the pass +54 shared lines; see [[#Typed assembly language]] | 2309 | 2868 | **1960** | 3836 |
| 2026-10-14 | X86ᵀ is the target of the typed pipeline (PR #58): typed select (CFGᵀ → X86ᵀ) proved in all five columns, ≃ in both graph models (the errors model's `Same` and its 1015-line boundary retired), equal results clock for clock in the interpreter; X86ᵀ semantics in each style (graph model 66, CEK and reduction 114, interpreter 110, graph model with errors 66); select 226 → 133, 313 → 111, 179 → 52, 313 → 111 and 1349 → 222, `SelectFacts` (37) retired. Untyped X86's semantics but its machine, and its adequacy, moved to `agda/Untyped/`; X86ᵀ adequacy direct in both graph models (679 and 1215, against 1240 and 2085 for X86); assurance, not in the totals: erasure to X86 keeps the meaning of every X86ᵀ program (CEK machines, PR #59) and select emits the instructions of select into X86. Graph model with errors 3776 → 2614 | 2131 | 2648 | **1818** | 3616 |
| 2026-10-14 | every compiler-correctness relation with the source on the left and the target on the right, and every per-pass ≃ as ⟦src⟧ ≃ ⟦tgt⟧ (`R D V′` for delay, the simplify relations, the tables of the later passes); the ≃-sym detours this made unnecessary are gone, the interpreter's converses `_≽_` and `_≽s_` deleted; the CEK and reduction simplify simulations, which run from the target, take the converse of the flipped relation (simplify 343 → 342, 572 → 574, 644 → 640, 710 → 716, 349 → 348; graph model select 133 → 134). Graph model with errors 2614 → 2613 | 2131 | 2650 | **1814** | 3622 |
| 2026-10-14 | delay's reflection relation in both graph models named the approximant logical relation (`R` → `ApproxLR`, `Obs` → `ApproxLRLayer`, the fuel tower `R′` → `ApproxLR≤`, `R′-irr` → `ApproxLR-depth-irrelevant`, the `R-…` lemmas → `ApproxLR-…`); no count changes | 2131 | 2650 | **1814** | 3622 |
| 2026-10-15 | the typed CEK machines (ISWIMᵀ, Clos2ᵀ–Clos5ᵀ) collect a tuple's values newest first in a vector, the tuple's length a reverse-append index (`_+ʳ_`, `_<><_` in `Framework/VecUtil.agda`, related vectors by `_<><₂_`), as in the ISWIMμ pilot, instead of in a list with an equation for its length: the semantics row 684 → 674 (reduction, which shares the Clos5ᵀ machine, 1068 → 1066), the lemmas shared by the passes 55 → 20 (`Common`'s length-equation lemmas gone, 30 → 9; `Clos5Common` 25 → 11), cast insertion 195 → 192, enclose 106 → 100, optimize 133 → 121, rco 150 → 149, lift locals 56 → 55; Clos5ᵀ adequacy in the graph model 739 → 715 (adequacy 2214 → 2190), the CEK proof the errors adequacy derives from 2192 → 2126; infrastructure +2 (`VecUtil` 10 → 12 with its `proof/` half). The interpreter (`evals` builds the vector in order), the reduction semantics (a tuple reduces in place) and the graph models collect no tuples, so they are unchanged (PR #67) | 2131 | 2582 | **1814** | 3620 |
| 2026-10-15 | ISWIMμ pilot P0 (not in the totals): a typed ISWIM with iso-recursive types, no recursion construct and no errors, ISWIMμ → Clos4μ (enclose, optimize, concretize, delay) in the graph model and the CEK machines, in `agda/Mu/`; against the same rows of the typed pipeline 908 → 842 and 800 → 730, graph-model delay 552 → 524 with ApproxLR's depth index still load-bearing; see [[#Current counts\|ISWIMμ pilot]] | 2131 | 2582 | **1814** | 3620 |
| 2026-10-15 | ISWIMμ pilot P1 (not in the totals): the back end, Clos5μ, Monμ, Impμ, CFGμ and the typed assembly language X86μ (no `chk`; a sum's case a pseudo-instruction), globalize to select, in the graph model and the CEK machines; row by row against the typed pipeline without simplify and cast insertion 1649 → 1543 and 1789 → 1655 (of the graph model's 106, 49 are X86μ's case); see [[#Current counts\|ISWIMμ pilot]] | 2131 | 2582 | **1814** | 3620 |
| 2026-10-15 | ISWIMμ pilot P2 (not in the totals): adequacy of the graph model for the ISWIMμ and X86μ machines (X86μ direct, no Clos5μ adequacy), 2190 → 1619 against the typed pipeline's; no-error lemmas for every semantics of ISWIMμ and X86μ (199 lines, in no total); the four columns state the same end-to-end theorem for `main : Int` (same constant, or both diverge), the graph model through adequacy, with no graph model with errors; `loc.py --mu` prints the four styles against each other (1577, 1673, **1020**, 2521); see [[#Current counts\|ISWIMμ pilot]] | 2131 | 2582 | **1814** | 3620 |
| 2026-10-15 | ISWIMμ pilot P3 (not in the totals): simplify on ISWIMμ (typed cp0, with `unfold` of a known `fold` as one more known-value rule), proved in all four styles and put in front of every composition (and so of adequacy's end to end): simplify rows 360, 584, 633, 715 against the typed pipeline's 342, 574, 640, 716; ISWIMμ's renaming kit shared between simplify and the reduction semantics (reduction semantics 995 → 965), ISWIMμ's continuity lemmas moved from adequacy to the graph semantics (355 → 375; adequacy 1619 → 1599); the pilot's totals 1958, 2258, **1653**, 3207 against 2064, 2390, 1719, 3320 for the typed pipeline without cast insertion; see [[#Current counts\|ISWIMμ pilot]] | 2131 | 2582 | **1814** | 3620 |
| 2026-10-15 | ISWIMμ is the main experiment (PR #70): its theorem statements in `agda/Mu/Theorems/` (graph model, simulation, interpreter, reduction, adequacy: 78, 38, 38, 38 and 29 lines, not in the totals) and its audit surface (1564, 1750, **1485**, 1940; adequacy 1891), closed by moving `AllProp` to `Mu/proof/Framework/` and splitting `Mu/Framework/ReductionAll.agda` into its definition (`red-∷`) and a proof half (ISWIMμ's reduction infrastructure 40 → 41, the new module line, in no total); `loc.py` prints ISWIMμ's tables by default and the ISWIM pipeline's with `--iswim`; no total changes. From this row on the columns are ISWIMμ's (the ISWIM pipeline's stay 2131, 2582, **1814**, 3620; see [[#Dynamic typing and errors]]) | 1958 | 2258 | **1653** | 3207 |
| 2026-10-15 | mixing semantics (not in the totals; see [[#Mixing semantics]]): simplify in the graph model, the other passes by the interpreters, joined by a bridge at ISWIMμ between its graph semantics and its interpreter (395, also ISWIMμ adequacy w.r.t. the interpreter, against 464 w.r.t. the CEK machine), 1839 in all; the splits that also prove globalize or explicate control in the graph model estimated at about 2500–3300; `loc.py --mixed`; no total changes | 1958 | 2258 | **1653** | 3207 |
| 2026-10-15 | the graph model's adequacy against the clocked interpreters instead of the CEK machines (reported separately, not in the totals; see [[#Adequacy]]): ISWIMμ's is the mixing experiment's bridge, moved to `Mu/proof/Adequacy/` (464 → 395); X86μ's direct against its interpreter (697 → 712; Clos5 values 307 → 301); end to end the interpreter column's statements, with no no-error lemma (22 → 15); adequacy 1599 → 1532, the graph model to running code 3557 → 3490; the CEK version kept as an alternative (`Mu/proof/Adequacy/CEK/`, in no total); the mixed total unchanged (1839, the bridge counted once); no total changes (PR #76) | 1958 | 2258 | **1653** | 3207 |
| 2026-10-20 | graph-model pass proofs shortened, no theorem statement changed: binder congruences whose bodies Agda infers (`lam-≃`, `let-≃`, `case-≃` on every nonempty consistent set, `Body-≃`), `ne-≃`, `guard-yes` and `body-mono`, in `Mu/proof/Semantics/Graph/Binders.agda` (semantics row, +17); rco's frame invariants in one record (`Ext`); concretize's tuple consistency from `con` of a tuple term; simplify 360 → 349, enclose 43 → 37, optimize 83 → 66, concretize 68 → 46, globalize 118 → 115, rco 125 → 109, lift locals 44 → 39, explicate control 71 → 64, select 83 → 76; adequacy 1532 → 1529 (`X86Compiled` uses rco's and lift locals' `code-rco`, `code-lift`) | 1884 | 2258 | **1653** | 3207 |
| 2026-10-21 | final cleanup pass of the other columns (PRs #88–#91, after the graph model's PR #87 above; no theorem statement changed, nothing moved into the infrastructure); loc.md refreshed. Interpreter (PR #88): simplify one induction for both directions at each clock (`sim`, `let-sim`) and one for the source running ahead (`run`) (633 → 508), globalize's environments by `All₂` (183 → 175), rco 85 → 83, the composition without four unused corollaries about Clos5μ (36 → 22). CEK (PR #89): the machines of ISWIMμ and Clos2μ–Clos4μ share their values (`Mu/Semantics/CEK/Values.agda`) and enclose, concretize and delay their value relation (`Mu/proof/Semantics/CEK/Rel.agda`, lemmas shared by the passes 11 → 38); simplify one `run` with `let-run` and `call-run` (584 → 560); semantics 575 → 511, enclose 93 → 71, optimize 127 → 128, concretize 111 → 88, delay 96 → 73, rco 147 → 120. Graph model (PR #90): delay around `Approx` and `Approx-fold` (524 → 450), composition 30 → 28, semantics 395 → 393. Reduction (PR #91): semantics 965 → 961, simplify 715 → 697, enclose 164 → 147, optimize 232 → 212, concretize 154 → 148, delay 139 → 126, globalize 219 → 192, rco 164 → 157, composition 20 → 18. Adequacy 1529 (its alternative for the CEK machines 1596 → 1599); audit surface 1548, 1669, **1468**, 1923 (adequacy 1773); mixed (a) 1848 → 1838. Also counted here, without rows of their own: the environment filler ⟨⟩ instead of ω (PR #85; graph model 1958 → 1961, `TypedOkBase` 90 → 92 in the infrastructure of both pipelines) and no contractiveness condition on μ (PR #86; ISWIMμ's languages and passes 938 → 921, `Type` 69 → 52; no total changes) | 1806 | 2103 | **1504** | 3093 |
| 2026-10-22 | Scott-domain column (not in the four-column totals; see [[#Scott domains]]): `inj` and `case` opaque (PR #93), a clean `make check-scott` 3057 s → 152 s, Scott total 3450 → 3457 (lemmas 132 → 135, delay 1403 → 1405, rco 195 → 197; infrastructure 1495 → 1507) | 1806 | 2103 | **1504** | 3093 |
| 2026-10-22 | Scott-domain cleanup (PR #95; no theorem statement changed, nothing moved into the infrastructure): one stage-indexed relation over a direction for both halves of delay, tags matched by `Same` (delay 1405 → 723); globalize with `with` in the recursion (262 → 147); select 204 → 133, rco 197 → 159, optimize 119 → 92, simplify 441 → 411, lift locals 63 → 59, concretize 62 → 58, enclose 50 → 49; Scott total 3457 → 2485; check 145 s | 1806 | 2103 | **1504** | 3093 |

**The typed pipeline (PRs #55, #56).** The third row from the end (the last two are the typed assembly language). The pilot (the two rows before it, see [[#Typed intermediate languages (pilot, superseded)]]) recommended inserting the checks early; phase 1 (PR #56) defined the typed languages and passes from untyped ISWIM to X86, phase 2 ported each column, and phase 3 made the typed pipeline the main one: the untyped modules moved to `agda/Untyped/` (module prefix `Untyped.`), the typed ones took the main names (`Compiler/Typed/X` → `Compiler/X`, `proof/Correctness/Typed/<style>/X` → `proof/Correctness/<style>/X`, `Theorems/Typed/X` → `Theorems/X`), and the pilot's statements (`Theorems/Typed.agda`) and composition (`compileᵀ`) were retired, the main statements subsuming them. The modules both pipelines use stayed in `agda/`; to keep them independent of the untyped languages, the frames and tables of X86's semantics (`Semantics/Graph/Frames.agda`, `Semantics/GraphErr/Frames.agda`), the X86 interpreter's values (`Semantics/Interp/Values.agda`), the X86 machine's frames (into `Semantics/CEK/Values.agda`) and `block-at` (into `Language/X86.agda`) were split off, and ISWIM adequacy lost the untyped compiler's corollaries (now `Untyped/proof/Adequacy/ISWIMCompile.agda`). That moves the untyped totals by a few lines (2608 → 2610, 3526 → 3521, 2794 → 2795, 3689 → 3684); the lemmas about X86's case that both graph-model select proofs had (`case-core`) are now shared, in `proof/Semantics/Graph/X86.agda`.

**Infrastructure audit, step 1 (PR #42).** The last row moves language-independent reasoning that the proofs had repeated, or had written locally, into the infrastructure, under the policy of [[#Language-independent infrastructure]]. No theorem statement, pass or semantics changed. What moved:

* **List lookups** (`proof/Framework/ListUtil.agda`, 98 → 114): `‼-pw`, lookup in pointwise-related lists (it was in `RCOFuel`, `LiftLocalsSim` and `LiftLocalsRed`, and as `lookup-pw` in `GlobalizeSim` and `GlobalizeFuel`); `reverse-map-‼`, lookup in the reverse of a mapped list (the tables of rco, explicate control and select instructions in the CEK and reduction proofs); `‼-any` (`RCOSim`, `RCORed`); and `args→list-hom`, listing the subterms of a tuple after a map over them, given its defining equation, which replaces `enc-list`, `opt-list`, `conc-list` and `simps-list` in the CEK proofs (`del-args` is a pointwise relation, not a map, and is kept).
* **Graph model:** `ρ₀`, the environment of a closed program (`Domain`; it was in `DelayFiniteCommon` and `SimplifyCorrect`), `ne-mem` (`SetsAsPredicates`; `DelayFiniteCommon`, `RCOCorrect`) and `Λ-≃` (`Ops`; word for word in `SimplifyCorrect` and `RCOCorrect`). `Clos5IswimContinuous` instantiates `SemanticsUtil` for `args-nth-mono`, `args-nth-cont` and `term-continuous` instead of repeating them (the semantics row, 734 → 716). Local copies of the environment lemmas `•-~` (`part` in `SimplifyCorrect`, `rel-ext` in `GlobalizeCorrect`, an extension in `RCOCorrect`) and `extend-nonempty-env` (five in `DelayPreserve` and `DelayReflectFinite`) were replaced by them.
* **Adequacy:** the runs of a step function from any state (`_↠_`, `_++↠_`, `↠-final-det`, formerly `Common.Runs`) are `proof/Framework/Runs.agda` (29 lines, used only by adequacy), and `terminates-det`, that a machine terminates with at most one observation, is proved once in `proof/Framework/Smallstep.agda` from `final-unique` (2 lines) instead of in the ISWIM and Clos5 adequacy proofs (ISWIM 684 → 651, Clos5 717 → 712).

The totals went down by 61, 26, 8 and 11 lines (graph model: semantics −18, simplify −12, delay −15, globalize −3, rco −13; CEK: 3 or 4 in each of seven rows; interpreter: globalize and rco −4 each; reduction: rco −7, lift locals −4), and adequacy by 38. The infrastructure grew by 59 lines (1866 → 1925): list lookups +16, the denotational framework +3, the graph model +9, the small-step framework +2, runs +29. Since the counts are by module, each proof is shown reaching all of a module it imports: the graph model reaches +28 lines of infrastructure (1310 → 1338), the CEK proof +18 (783 → 801), the interpreter +16 (729 → 745), the reduction proof +18 (967 → 985), and adequacy +59 (1462 → 1521).

**A fourth column (PR #37).** The last two rows. The first is the CEK code regrouped so that the reduction column can share the machines of Imp, CFG and X86 and the proofs of explicate control and select instructions: the values of the Clos5 machine, which the Imp and X86 machines use, moved to their own module (+1 line, the module line, in the semantics row: 656 → 657), the list lemma `‼-map` from `RCOSim` to `ListUtil` (rco 414 → 410), and the end-to-end theorems for `compile-cfg` and `compile-x86` from `ExplicateSim` and `SelectSim` to `CompilerX86Sim` (explicate control 129 → 127, select instructions 240 → 238, composition 19 → 24); in all 2908 → 2906. The infrastructure grew by 344 lines: the substitution library (189 with `ScopeSubst` and `SubstRel`) and the reduction framework (130), used only by the reduction column, and in the shared infrastructure the `runs` answer of the small-step framework (+9) and three list lemmas (+16). See [[#Reduction semantics + simulation]].

**Import statements (PR #35).** The last two rows are the same code counted two ways: from PR #35 on, import statements are not counted. With them, the split into an audit surface and `agda/proof/` cost the denotational total 80 lines, 61 of them module lines and imports of the new proof halves; reducing them would have needed re-export modules that add dependencies between files, or merged modules. Imports measure how finely a development is divided into modules more than what it proves, and the denotational proof is divided most finely: imports were 19% of its total, against 13% and 17% for the simulation and interpreter ones. Without them the totals go from 3617, 3345 and 2477 to 2942, 2908 and 2062 (−675, −437, −415), adequacy from 3719 to 3168, and the infrastructure from 1788 to 1453. The counts in the sections below are as of their PRs, with imports.

**Adequacy for X86 (PR #33).** The X86 machine and interpreter now do what the X86 semantics says at calls (see [[#Select instructions]]): the callee starts with `%rax` unset and no flag, `callq` goes wrong if `%rdi` or `%rsi` is unset, and `retq` goes wrong if `%rax` is unset, also when it returns to a caller. This cost the machine semantics 3 lines (the machine) and saved the interpreter select proof 2 (its hypothesis on calls lost the registers); `SelectSim` and `SelectFuel` still need no precondition. Adequacy went from 2187 to 3707 lines: X86 +1243, well-formedness 60 → 328, end to end 24 → 39, ISWIM +2 and Clos5 −8 (the runs of any machine are now shared, `Common.Runs`, and the Clos5 machine's values, which X86 shares, are in `Values.agda`, used by both); the list lemmas it needed went to `ListUtil` (infrastructure, 62 → 92 lines, also used by Clos5 adequacy).

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

**Late code check in Clos4 and Clos5 (PR #26).** The Clos4 and Clos5 machines and interpreters now check that the operator of `app ⦅ L , M , N ⦆` is code at the call, after evaluating all three operands, instead of right after L; ISWIM, Clos2 and Clos3 keep the early check. This is what rco needs to preserve going wrong (see [[#Caveats]]). The denotational proof is unchanged. Per module:

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

*ISWIMμ:* rco is Clos5μ → Monμ (`Mu/Compiler/RCO.agda`), monadic by construction and with typed, well-scoped terms, so no proof needs `Scoped` or a late code check: 109, 120, 83 and 157 lines (`Mu/proof/Correctness/<style>/RCO*.agda`; see [[#Current counts]]). The rest of this section is the untyped pipeline's.

The pass (`Compiler/RCO.agda`, Clos5 → Clos5, shared) binds every complex operand of a construct to a fresh variable by a `let`, left to right, and leaves atoms (variables, literals, code pointers) in place, shifted under the new lets; the result is in monadic normal form (`Language/Mon.agda`). It adds no calls and `let` does not tick. The late code check in the Clos4 and Clos5 machines and interpreters (see [[#Caveats]]) was added for this pass: with the check right after the operator, `app ⦅ L , M , N ⦆` with a non-code L errors before M runs, while its rco, `let x = L in let y = M in …`, would run M first.

* **Reduction (278 lines):** see [[#Reduction semantics + simulation]].
* **Denotational (237 lines): an exact equation.** `rco-correct : ⟦ rco M ⟧[ T ] ρ ≃ ⟦ M ⟧[ T ] ρ` for nonempty ρ, and `rco-program-correct : ⟦ rco-program P ⟧ₚ ≃ ⟦ P ⟧ₚ` for **every** program, with no scoping precondition. The laws are that `let` is strict and otherwise substitutes the meaning of its right-hand side (`let-strict`, `let-β`, which uses the continuity of Clos5), and that every construct whose operands rco names is a strict congruence (`Strict`); one lemma for the let chain (`lift-≃`) then gives each construct in one line. Order of evaluation is invisible: an error and divergence both denote ∅, and an unbound variable denotes {ω}.
* **Simulation (449 lines).** A forward simulation of the Clos5 machine by itself, for programs in `Scoped`. The target environment has the values of the lets in front, so terms are related up to a renaming (`Ren`). The source frames of a construct are related to the target's remaining let chain by `Pend` (one constructor per operand: a complex operand runs in lock step under a let frame, an atom is evaluated by the source while the target waits, with a decreasing index, and at the end the target runs the construct on its atoms up to the same final frame, `retT`).
* **Interpreter (298 lines): clock for clock, with equality of results.** For `Scoped` programs, `eval ds ck ρ M ≡ eval (map rco ds) ck ρ (rco M)` for every clock (`run≈`): values contain no code, so they are equal, not just related. The key lemma is the let chain (`lets≈`): evaluating the chain evaluates the complex operands left to right and then the construct with the atoms bound to their values; renaming commutes with evaluation (`ren`).

**Why the operational proofs need `Scoped`.** An atom left in place is evaluated after the complex operands that follow it. An unbound variable errors when it is evaluated, so it would error later: ``pair (` 0) L`` with L a loop errors in the empty environment, while its rco, ``let x = L in pair (` 1) (` 0)``, diverges. In the denotational semantics both denote ∅, so the equation holds anyway. `Scoped` (main closed, each definition in its two parameters) rules this out; the compiler produces such programs (`compile-scoped`, 249 lines, counted in the operational totals because only their `compile-mon` theorems use it, plus the 29 of `Syntax/ScopeRename`, now infrastructure).

The sizes in this section are as of PR #26 (now 243, 449 and 298).

## Lift locals

*ISWIMμ:* Impμ's frame is typed by the context of the Monμ term, so lift locals keeps the variables as they are: 39, 51, 27 and 204 lines (the reduction column still relates a reduction semantics by substitution to the frames of the Impμ machine). The rest of this section is the untyped pipeline's.

The pass (`Compiler/LiftLocals.agda`, shared, 44 lines) takes a monadic Clos5 term to Imp (`Language/Imp.agda`, shared, 35 lines). Imp has no binders: each body declares a frame of slots, a variable names a slot, `let` becomes the assignment `x := e₁; e₂`, and `case` assigns the payload to a slot. The frame is threaded: an assignment is seen by everything that runs after it in the same frame, also after the expression that contains it. A call runs the callee in a fresh frame (free variables in slot 0, argument in slot 1) and leaves the caller's frame as it was; reading or assigning a slot beyond the frame errors. Slots are de Bruijn levels: the variable x at depth d is slot d ∸ (x + 1), and a `let` or `case` at depth d assigns slot d, so code at depth d assigns only slots that no variable in scope names. The frame has d₀ + height slots (height = deepest nesting of binders), and a variable out of scope becomes slot n, beyond the frame. No proof needs a precondition, and the semantics of Imp in each style is new. As of PR #27 (since then, the denotational proof is against a continuation-passing semantics of Imp, and what follows describes the direct one, now an experiment; see [[#Explicate control]]):

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

*ISWIMμ:* Impμ → CFGμ, ≃ in the graph model against the continuation-passing semantics of Impμ (as Impᵀ's), 64, 105, 75 and 105 lines (the CEK proof is the reduction column's too). The rest of this section is the untyped pipeline's.

The pass (`Compiler/Explicate.agda`, shared, 37 lines) takes Imp to CFG (`Language/CFG.agda`, shared, 28 lines), a C-like language after Essentials of Compilation. Imp's expressions without control flow became `Simple` (`Language/Imp.agda`), shared by the two languages. A CFG body has a frame size, a list of blocks and a start. A block is a tail: assignments `x := s` of simple expressions, ending in `return s`, `goto l`, or `case a x l₁ l₂`, which assigns the payload of a to slot x and jumps to l₁ or l₂. Blocks are listed newest first, as Clos5's global definitions are, and a block jumps only to older blocks, so control flow within a body is acyclic: no semantics needs a fixed point over the blocks, and the clocked interpreter does not tick at a goto (it recurses on the list of older blocks). The pass is in continuation-passing style (Danvy): `explicate-assign e x k` translates `x := e` followed by the tail k; a nested assignment `y := e₁; e₂` becomes `y := e₁` followed by `x := e₂` followed by k, and a case gets a join block that holds k, which its branches reach by `goto`, so k is not duplicated. `explicate-tail` translates an expression in tail position. The pass threads the list of blocks, only adding to it, so a tail refers only to blocks made before it.

| component | denotational: graph model | CEK machine + simulation | clocked interpreter + value relations |
|---|---:|---:|---:|
| semantics of CFG | 37 | 50 | **32** |
| explicate control | 210 (106 + 104) | 152 | **145** |

The CFG machine and interpreter reuse the evaluation of simple expressions factored out of the Imp machine (+12 lines there) and interpreter (+4); the denotational CFG semantics reuses `Semantics/Graph/Imp.agda`. No proof needs a precondition.

* **Simulation (50 + 152): a forward simulation with a measure** (`ExplicateSim`). The two machines share the frame and the evaluation of simple expressions and run in lock step except for the control flow that the pass makes explicit. An Imp expression runs as the tail that explicate makes of it in the mode of its continuation: `explicate-tail` in tail position, `explicate-assign e x k` when its value is assigned to x before k runs. So the stack of Imp continuations `x := □; e₂` is a CFG tail (`Ctl`: the tail made of e₂, or a `goto` to the join point that runs it). Imp's step into an assignment `x := e₁; e₂` has no CFG step: e₁ already runs as the tail the assignment runs as. This stutter is measured by the nesting of assignments (`depth`). A value returned to `x := □; e₂` is matched by the assignment and the chain of gotos to join points (`join`), a case by its jump to a block (`Br`). A tail made at the blocks bs runs with any newer blocks (`block-≼`).
* **Interpreter (32 + 145): clock for clock, with equal results** (`ExplicateFuel`). The pass keeps every call and gotos do not tick, so the interpreters tick in lock step; values are Clos5's in both, and code k names definition k of either program, so results are equal. `Means bs t K`: t, run with any blocks cs ⊒ bs, returns K applied to the frame. The CPS lemma (`assign-ok`): if k means K, `explicate-assign e x k` means running e, assigning its value to x and then K; `explicate-tail e` means the value of e (`tail-ok`); jumps to the join point run k with the blocks it was made with (`jump-at`).
* **Denotational (37 + 210): a congruence** (`ExplicateCommon`, `ExplicateCorrectK`), `explicate-correct : ⟦ explicate P ⟧ₚ ≃ ⟦ P ⟧ᴷₚ` for every program. A CFG tail, given the meanings of the blocks it can see and a store, means a set of values; the blocks of a body get their meanings newest first, as global definitions do, each with the meanings of the older ones, so no fixed point is needed (`Semantics/Graph/CFG.agda`). Against the continuation-passing semantics of Imp, the tail that `explicate-assign e x k` makes means e run with the continuation that assigns x and runs k, `⟪ explicate-assign e x k ⟫ ≃ ⟦ e ⟧ᴷ (assignK x ⟪ k ⟫)`, and `explicate-tail e` means e run with `halt`. Each case is a congruence: a nested assignment is e₁ with the continuation that assigns y and runs e₂ on both sides, and a case passes the continuation to its branches, which in CFG reach it through the join block. The common module (106) has what the proofs against both Imp semantics share: a tail made at bs means the same with newer blocks (`≼`, `blocks-at`, `goto-≃`, `Stable`), atoms and simple expressions, and the end-to-end theorems `compile-cfg-correct-const` and `-nonempty`.

**The counterexample, and consistent binders.** Explicate control is a commuting conversion: it moves the continuation of an assignment into the branches of a case. With the graph model as it was, where Λ and 𝒞 bind any finite set, the equation ⟦explicate P⟧ ≃ ⟦P⟧ was false, and a machine-checked counterexample showed it (`ExplicateCounterExample`, since removed). Take the Clos5 code `λ fv. λ Y. let y = case Y of inl _ ⇒ ⟨1,1⟩ | inr _ ⇒ ⟨2,2⟩ in ⟨fst y, snd y⟩`, lifted into Imp. The inconsistent argument Y = {left ν, right ν} makes the let bind y to a mix of the two branches, so ⟨1,2⟩ is a result in Imp but not in CFG, where each branch reaches the join point on its own. Such junk entries, elements that no run of a program produces, did not break the equations of the earlier passes; the commuting conversion is where they broke one. The fix was to the domain, not to the pass: Λ and 𝒞 now bind only consistent finite sets, so a denotation under a consistent environment has no inconsistent elements (see [[#Caveats]]; +96 denotational lines, +74 adequacy, with delay 16 shorter). Separately, assigning beyond the frame in the denotational Imp and CFG now means ∅, as the machines error, instead of `init`, a value after which the program still ran: Imp checks the slot before the right-hand side runs and CFG after, and with `init` the pass could not preserve meanings.

**Two semantics of Imp.** Both are kept. In the direct semantics (`proof/Semantics/Graph/ImpDirect.agda`, from lift locals), an expression means a set of values and an output store. In the continuation-passing one (`Semantics/Graph/ImpK.agda`), `⟦ e ⟧ σ κ` runs e in the store σ and gives its value and the store it leaves to the continuation κ, the meaning of the rest of the body; the store is never collected over the runs of an expression. `Semantics/Graph/Imp.agda` (58) has what both share. With the direct semantics the commuting conversion is in explicate control: in Imp, `x := e; k` runs k in the store e leaves, collected over all runs of e, while in CFG k runs after each run on its own. Each step is a law (`let-assoc`, `let-case`); one direction is monotonicity, the other needs CFG tails to preserve directed unions of stores (`Dir`, `DC`) and the bound sets to be consistent, so that the finitely many runs k used can be merged into one (`merge`), and Imp to be monotone and consistent (`I-mono`, `I-con`). With the continuation-passing semantics, explicate control is the congruence above, and the commuting conversion moves into lift locals, against Clos5: the continuation commutes with let and with case (`let-law`, `case-law`, in `LiftLocalsCorrectK`), two small laws resting on the monotonicity and consistency of Clos5 (`Clos5IswimContinuous`). The chains, with the common modules counted in both denotational rows:

| | semantics of Imp | semantics of CFG | lift locals | explicate control | chain |
|---|---:|---:|---:|---:|---:|
| denotational, continuation-passing (main) | 84 (58 + 26) | 37 | 275 (105 + 170) | 210 (106 + 104) | 606 |
| denotational, direct (experiment) | 96 (58 + 38) | 37 | 213 (105 + 108) | 665 (106 + 559) | 1011 |
| simulation | 108 | 50 | 218 | 152 | 528 |
| interpreter | 65 | 32 | 143 | 145 | 385 |

The direct semantics makes lift locals smaller (213 against 275) and explicate control much larger (665 against 210): the store merging, directed continuity over stores, and the monotonicity and consistency of Imp are all in explicate control. With the continuation-passing semantics the denotational chain is 606 lines, against 528 (simulation) and 385 (interpreter); with the direct one it is 1011, about twice the simulation chain. The commuting conversion is where the graph model's junk entries broke the equation, and it is where the choice of the semantics of Imp matters most: done against Clos5's binders it costs two small laws, done against stores it costs the bulk of the direct proof.

## Select instructions

*ISWIMμ:* CFGμ → X86μ, a typed assembly language (see [[#Typed assembly language]]) with no check, and a sum's `case` one pseudo-instruction: 76, 107, 48 and 107 lines (the CEK proof is the reduction column's too), with no precondition. The rest of this section is the untyped pipeline's.

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

*ISWIMμ:* adequacy for the X86μ interpreter is direct, 712 lines, with 35 for the compiled programs' conditions (`X86Compiled`), and the end-to-end theorem goes from ISWIMμ adequacy, `compile-x86-same` and X86μ adequacy (see [[#Adequacy]]); the alternative for the X86μ machine is 697 lines. The rest of this section is the untyped pipeline's.

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

*ISWIMμ:* the policy below is unchanged; ISWIMμ adds heterogeneous vectors and the reduction of their operands (`Mu/Framework/`, `Mu/proof/Framework/`), the counterparts of vectors and `ReductionVec` (see [[#Infrastructure]]).

Code that other languages and compilers would use unchanged is reported in its own table and is not in any total. It is what a textbook or a verified compiler sets up once, before any particular language: Schmidt's semantic algebras and Winskel's metalanguage of domain constructions play this role for denotational semantics, and CompCert's general-purpose libraries and its generic transition systems and simulation diagrams (`Smallstep.v`) for the simulation style. The test is applied evenly to the four styles: would another language or compiler reuse the module as it is?

* **Infrastructure:** the abt library and the lemmas about the syntax of any signature (`Syntax/`: renaming, scoping, uses), list lookups (`ListUtil`), base types and `_⇔_` (`Primitives`, `Iff`); the denotational framework (sets as predicates, environments, the semantics of any signature and its monotonicity and consistency, `RenameSem`); the graph model, `GraphModel/` (formerly `Compiler/Model/Graph/Domain/ISWIM/`: values and consistency, the operators with their monotonicity, consistency and continuity, continuity of a semantics in its environment, formerly `Sem/Continuous`); the small-step framework (`Smallstep`, `Simulation`) and the clocked one (`Clocked`), both now parameterized over the type of observations (and, for `Clocked`, the observation of an error); since PR #37, substitution for any signature and its σ-calculus lemmas (`Syntax/Subst`, `Syntax/ScopeSubst`), the closure of a relation on terms under renaming and substitution (`Syntax/SubstRel`), and the reduction framework (`Reduction`: reductions as step functions with congruence rules, frames, answers, and the end theorem), which only the reduction column uses.
* **Not infrastructure:** the meaning of this compiler's primitives (`Semantics/Graph/Prim.agda`: `out`, `primD` and its lemmas), which stays in the denotational semantics row, as `prim?` stays in each machine and interpreter; this compiler's observations (`Semantics/Observation.agda`) and the instances of the operational frameworks at them (`Semantics/CEK/Smallstep.agda`, `proof/Semantics/CEK/Simulation.agda`, `Semantics/Interp/Clock.agda`, `Semantics/Reduction/Smallstep.agda`). The operational values are not infrastructure either: each language's `Val` is its own small datatype, closures over that language's terms or code pointers into its tables, observed through this compiler's observations, so no other language would reuse it as it is.
* **What it changed in the totals:** the rows "generic infrastructure" and "domain, operators, continuity" are gone, and so are the shared modules that became infrastructure; see [[#History]].

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

(As of PR #28; see [[#Current counts]] for the current table.) The denotational proof relies on twice as much infrastructure as the simulation one: the graph model and the denotational framework (907 lines) against the small-step framework (187). As of PR #37 the reduction proof relies on 952 lines of it, 319 of them its own (substitution 189, the reduction framework 130). Adequacy uses 1519 lines of it, 158 of them (`Smallstep`, `Iff`, `Syntax.Scope`, `Syntax.ScopeRename`) not used by the denotational proof.

## The interpreter proof

*ISWIMμ:* the interpreters are typed (`Mu/Semantics/Interp/`), total functions of typed terms to typed values with no `error` result, and every pass but simplify is proved clock for clock as below. The rest of this section is the untyped pipeline's.

Each interpreter is `eval : ℕ → Env → AST → Result Val`, where `Result Val` is `timeout`, `error` or `ret v`. It is defined by recursion on the clock and the term. The clock goes down only at a function call, and a call with clock 0 times out. The interpreter errors exactly where its machine stops with an error, and it evaluates in the same order: left to right, with the operator checked to be a function before the argument is evaluated (in Clos4 and Clos5: at the call, after all three operands).

Except simplify, no pass adds or removes function calls. Enclose, optimize, concretize and globalize map each application to one application. Delay maps it to a `let` around one application, and `let` does not tick. So every pass but simplify is proved **clock for clock**: for every clock, the program and its compilation both time out, both error, or both return related values. A generic lemma (`clocked`, 17 lines) turns this into both directions of the end theorem. There is no determinism argument and no simulation diagram. Simplify removes calls, and is proved clock-monotone instead (`clocked-le`; see [[#Simplify]]). The end theorem `compile-correct` in `CompilerFuel` composes the six results with `equiv-trans`, for the same `compile` and the same precondition (a closed ISWIM program) as `CompilerSim`.

The value relations and environment agreements are the same as in the simulation proofs. The saving is in everything the machines add: the continuation relation, one case per frame, and the states where one machine is ahead of the other. Pass by pass (interpreter against simulation):

* **enclose (162 against 222).** The difference is the continuation relation and the per-frame cases: a step of a frame becomes a `>>=` and `bind-rel`. Building a closure takes several Clos2 steps for one ISWIM step, which the machine proof matches by a plus; the interpreter just evaluates the captured variables.
* **optimize (194 against 273).** The source evaluates the free variables that the optimized closure drops, and the target does not. The machine proof needs a measure simulation: a match indexed by a natural number that each such stuttering step decreases, with states for the middle of dropping a variable. The interpreter has **no stuttering index**: a dropped free variable is a variable, which makes no call and, in a well-scoped program, cannot error, so the two interpreters call functions in lock step.
* **concretize (152 against 218).** A free variable becomes a projection from the tuple, three Clos3 steps for one Clos2 step, and building a closure takes one extra step. The machine proof relates a Clos2 state to a Clos3 state that is ahead of it (`Reach`, `enter`). The interpreter proof has **no run-ahead states**: a projection ``get i ⦅ ` 1 ⦆`` and the tuple of free variables are each evaluated in one go, with no intermediate state to relate.
* **delay (116 against 168).** An application becomes `let x = L' in app (fst x) (snd x) (shift M')`. The machine proof needs the run-ahead state `retT` and the four administrative steps that reach it. The interpreter proof has **no run-ahead state**: the `let`, `fst` and `snd` compute away, and `let` does not tick.
* **globalize (134 against 189).** Both proofs use the same **table-indexed relation**: the Clos5 program runs with the table D that the pass made for the whole program, the relation is indexed by D, and code `fun N` is related to `code k` when the table made by globalizing N is part of D. The lemmas about growing tables are shared. The difference is again the continuation relation and the frames.
* **composition (37 against 32).** Agda cannot infer the intermediate programs through the interpreters' `sem`, so the interpreter composition names them.

As of PR #26 (rco), the clocked interpreters (364 lines) are smaller than the machines (471): no continuations and no states. The generic part (80 lines against 188, now infrastructure: `Clocked` 80, `Smallstep` and `Simulation` 187) has no transition systems, simulations or determinism lemmas. In all, the interpreter proof was 1980 lines against 2653, both counting the 443 lines of shared syntactic lemmas and observations that only the two operational proofs use (165 before rco).

## Why delay costs more on the denotational side

*ISWIMμ:* delay costs 450 lines in the graph model against 73, 35 and 126, with the approximant logical relation and its depth index (`ApproxLR`; the fundamental lemma in the form `Approx D D'`, built by `Approx-fold`), which recursive types need (see [[#Dynamic typing and errors]]). The analysis below, for the untyped pipeline, explains why the graph model must reflect.

As of PR #24, before arithmetic; the denotational proof of delay was 824 lines and the simulation one 151 (now 859 and 168, see [[#History]]).

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

*ISWIMμ:* the reduction column is as described below, on the typed languages ISWIMμ–Clos5μ (`Mu/Semantics/Reduction/`), with heterogeneous vectors of operands (`Mu/Framework/ReductionAll.agda`); it is the largest column (3093). The numbers below are the untyped pipeline's.

The fourth column replaces the CEK machines of the languages with binders (ISWIM, Clos2–Clos5) by reduction semantics by substitution, and keeps everything else of the simulation style: the same observations, the same end theorem (`Equivalent`), forward simulations, and backward simulation from determinism. So the comparison with the CEK column isolates the choice of semantics.

**The semantics.** A state is a term. `red : AST → Red AST` says whether a term is a value, is stuck, or reduces, and a program's machine runs it (`Framework/Reduction.agda`). It is written with congruence rules: `step-in f (red X) k` reduces the subterm X in the context f, is stuck if X is, and continues with k if X is a value; so `red (app L M) = step-in (app □ M) (red L) (app? L (red M) M)`. This was chosen over evaluation contexts as the more compact: one function per language, with no decomposition into a context and a redex, no plugging, and no unique-decomposition lemma, deterministic and total by construction as the machines are; lifting a run of a subterm through a context is one generic lemma (`star-in`, `plus-in`) for any frame, a function g with `red (g X) ≡ step-in g (red X) (κ X)`. β, case and let substitute values (`Framework/Syntax/Subst.agda`, generic for any signature; cleared code, ∁, is not entered). Order of evaluation and the checks are those of the machines: the operator of an application is checked to be a function before the argument in ISWIM, Clos2 and Clos3, and only at the call in Clos4 and Clos5. A variable is never looked up: one that is reached is unbound, and errors. The reduction semantics (291 lines) are smaller than the machines (390), but need a predicate for their values and its two lemmas (120).

Imp, CFG and X86 have no binders: a reduction semantics for them would be a configuration-stepping machine on frames and blocks, which is what their CEK machines are. So the reduction column keeps those machines, and the proofs of explicate control and select instructions between them are the CEK column's, shared: they are counted in full in both columns (the semantics row includes the 267 lines of the three machines, and the two rows are the CEK proofs), so the sharing is no advantage to either.

**The simulations.** A relation on terms is a simulation when the reduction of every source term is answered by every related target term (`Ans`, `proof/Framework/Reduction.agda`): a value by a run to a related value, a stuck term by a run to a stuck term, a step by one or more steps to a related term. Congruence (`ans-in`) answers a construct from the answer of its operand, and the end theorem (`red-equivalent`) gives `Equivalent`. The target may have to take administrative steps before it stops (a projection in concretize, a let in delay, the evaluation of atoms in lift locals), so the small-step framework now also answers a stop by a run to a final state (`runs`; see [[#Caveats]]).

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
* **What substitution costs, and saves.** Enclose (+28), delay (+37) and globalize (+33) cost more than the CEK proofs: the relation on terms and its closure under substitution replace the relations on environments and continuations, and the congruence cases are about as many as the CEK proofs' frames. Enclose also tracks that the target stays closed, so that a closure whose captured variables were substituted is a value. Optimize is even: the reduction has no stuttering (a dropped free variable is a value after substitution, and takes no step, where the CEK machine evaluates it), but needs `Pr` for the closure's free variables and the closedness of the source. Concretize is smaller (−24): its run-ahead states (a variable becomes three Clos3 steps) become one clause, a value is related to a projection from the tuple of free variables, which takes one step. Concretize needs a new precondition, a well-scoped program (see [[#Caveats]]).
* **rco needs no closure under substitution** (−132 against the CEK proof). Its values are equal on both sides (they contain no code), so a complex operand M in the context h of its construct is related to its let in the target, `h[M] ≈ let x = M' in B`, when M ≈ M' and `h[V] ≈ B[x := V]` for every value V. The quantification is over a term, the same on both sides, so the relation is strictly positive and not a logical relation, and the simulation recurses into it. Every substitution is that of a β, a case or a let into code, related by `rco≈` (sub σ M ≈ sub σ (rco M) for σ mapping to values), which builds the let chains of rco by recursion on the operands (`chain`, 101 lines with the left-to-right frames of the constructs). The CEK proof needs renamings of environments and the pending chains (`Pend`) instead.
* **Lift locals costs most** (+137): it is the boundary between substitution and frames. The source is a term in a context of lets, the target an Imp state with a frame and a continuation, so the relation pairs the source's context with the target's continuation (`Kont`, as in the CEK proof), and values are related as data (term values with machine values). The source takes no step to evaluate an atom, which is already a value, while the target takes two, so each construct matches one source step with the target's evaluation of all its operands, case by case (the operands bound or not, and the shape of the values).

**Reading this column against the others.**
* **"Reduction semantics" here is substitution-based structural operational semantics**, a step function with congruence rules, not Felleisen–Hieb evaluation contexts (see *The semantics* above). A version with evaluation contexts would add decomposition, plugging and unique decomposition; it was not built, so its cost is not measured.
* **Substitution is infrastructure, so it is outside the total**, by the same rule that keeps the graph model out of the denotational total. The substitution library (189 lines, with `ScopeSubst` and `SubstRel`) and the reduction framework (130) are used only by this column; they are its counterpart of the graph model and denotational framework (767 lines), and like them they would be reused unchanged by another language. Both are in the infrastructure table.
* **About a fifth of the total is the CEK column's code.** The machines of Imp, CFG and X86 (267 lines) and the proofs of explicate control and select instructions (127 + 238) are the same files in both columns, 632 of the 3011 lines. The comparison of the two semantics is in the rows from enclose to lift locals, and the semantics row's reduction part (411 lines against the machines' 390).
* **The per-pass theorems differ in one place:** concretize is stated for well-scoped programs (`WS 0 M`), which the CEK theorem does not require (see [[#Caveats]]). The end-to-end theorems are the same as the CEK ones.

**The prediction** of [[#Which relations each proof needs]] was that with substitution the closure-conversion passes would need relations on terms closed under substitution rather than the compilation function, that rco would too, and that lift locals, explicate control and select instructions would be unaffected. It held for the closure-conversion passes, with a refinement: the relation must be closed under substitution, but on the code of closures, which substitution never enters, the compilation function is still the relation (through a fundamental lemma quantifying over substitutions). It did not hold for rco, which needs no closure under substitution because its values are equal, and is smaller than the CEK proof. Lift locals is affected after all, as the pass from substitution to frames; explicate control and select instructions are indeed unaffected, and shared.

## Simplify

*ISWIMμ:* simplify on ISWIMμ is the same optimizer, typed, with one more known-value rule (`unfold` of a known `fold`): 349, 560, 508 and 697 lines (see [[#Current counts]]). The rest of this section is the untyped pipeline's.

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
* **Reduction** (`proof/Correctness/Reduction/SimplifyRed.agda`): the target takes fewer steps than the source, since simplify did some of the source's reductions ahead of time, under binders. So the simulation goes **from the target to the source**: each target step is answered by one or more source steps (the source catches up with the reductions simplify did, then takes the same step), with the existing framework (`red-equivalent`), and `Equivalent` is symmetric (`equiv-sym`). No stuttering is needed: values are terms, so a duplicated small value takes no steps. The relation (source on the left, `_≽_`) is a congruence closed under substitution (`SubstRel`, as for the closure-conversion passes) with two more rules: *step*, the source reduces first; and *let*, a let of a value that simplify kept bound and known, whose bodies are related only after β (`N[W] ≽ N'[V']`). Since simplify reduces under binders, the source's catching up happens on open terms, where a variable stands for a value: a reduction `⟶` of open terms (14 rules; 16 since PR #43), closed under substitution, which in a closed term is a step of the reduction semantics (`closed-red`) and keeps it closed; 130 lines in all. The main lemma takes two substitutions, the source's τ and the target's υ (the let rule substitutes a different value on each side), and a known value of a term is reached by the source (`eval-sv`: a term related to a value steps to a related value). The proof also has the values of the ISWIM reduction (25 lines; only simplify needs them). Its simulation (105 lines) is the shape of the other reduction proofs.
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

* **Graph model.** The semantics row is the expensive one (+28: the clause in three languages, its monotonicity and consistency, and the continuity of ISWIM and Clos3), since each language needs its instance of every property. The passes that map `let` to `let` cost one congruence each (2–6 lines), by `⋆-≃` and the infrastructure's `Λ-≃` (PR #42), which compares bodies on the sets `Λ` binds; enclose and optimize lift their renaming of the environment under a binder to the top level, shared by `case` and `let`. Simplify cost 5 lines (3 of them the `let` cases of the syntactic lemmas in `SimplifyFacts`, in every column): in the graph model the emitted `let` means the same as the residual it replaces, and a source `let` means the same as a β-redex, so the β lemma is the one for `let`. **Delay is the exception (+48).** Its two directions are not equations: preserve needs β for a target `let` (by continuity; about 14 lines with its case), and reflect, over finite lists of target observations, must first gather the finite parts of the operand that the target's results use into one list (`let-collect`), then use β for a source `let` (about 34 lines). This is the same cost as for application in that proof (see [[#Why delay costs more on the denotational side]]), at a smaller scale.
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
  * backward, the approximant logical relation `ApproxLR D V'`, between a source set and a finite target approximant (a finite list of target values), by recursion on the depth of the approximant, encoded with fuel (`ApproxLR-depth-irrelevant`: the fuel does not matter).

  Domain values contain functions, so a function entry is related by quantifying over related arguments. These are true logical relations.

**Simulation.**
* Every pass needs a state relation, since a forward simulation is stated through one.
* Five passes also need a relation on values: the closure-conversion passes. Machine values contain syntax, a closure being code plus an environment, and those passes rewrite that syntax.
* The four Essentials of Compilation passes compute identical values. Their relations are about environments, frames, continuations and step timing.
* None of the value relations is a logical relation. Each is an inductive type defined by structural recursion on first-order values. A closure is related by naming its code (`enclose N`, `delay N`, a table entry) and relating its captured values, with no quantification over arguments. That is why the simulation delay proof is cheap.

**Interpreter.**
* The same five passes define a value relation `_≈_`, nearly identical to the simulation one; for globalize it matches constructor for constructor. The other four use equality.
* None are logical relations, for the same reason as in the simulation proofs.

**Reduction.** See [[#Reduction semantics + simulation]]. The term relation is also the value relation, values being terms; none of its relations is a logical relation (rco's let chains quantify over a value term, the same on both sides).

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

**With a reduction semantics (substitution) instead.** This was the prediction before the reduction column was built (PR #37); see [[#Reduction semantics + simulation]] for what it found. I expected the code part to stop being the compilation function for the closure-conversion passes:
* After a β-step the source term is `N[V/x]`. In general `pass(N[V/x]) ≠ pass(N)[V'/x]`, because optimize, concretize and enclose compute capture lists and layouts from free variables, which substitution changes.
* Intermediate terms also contain runtime values and administrative redexes that the pass never produced, such as rco's half-reduced let chains.
* Those passes would then need an inductive relation on terms, closed under substitution of related values, as in Plotkin's colon translation for CPS.
* Lift locals, explicate and select would be unaffected: Imp, CFG and X86 use frames and stores, not substitution.
* The denotational proofs would be unaffected too, since they never mention machine states.

**Summary.** The denotational side needs a value relation in one pass instead of five. But that one is a pair of logical relations, one of them over finite observations, and it costs most of the denotational delay proof (see [[#Why delay costs more on the denotational side|above]]).

## Experiment: a direct backward simulation for delay

The numbers in this section are as of PR #24, before arithmetic, which added 3 lines to `DelayBackSim` (149) and 17 to `DelaySim` (168); see [[#History]].

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

*ISWIMμ:* has no counterpart: ISWIMμ has no errors, and the plain graph model with adequacy states the operational theorem (see [[#Adequacy]] and [[#Dynamic typing and errors]]).

As of PR #53. The **graph model with errors** is a denotational semantics in which an error and divergence differ: a program that stops with an error denotes a set that holds ω, one that diverges denotes ∅. Since PR #51 it is defined for every language of the compiler, every pass is proved correct in it, and it is adequate for the ISWIM, Clos5 and X86 machines on all three outcomes. It is the fifth column of [[#Counts of the ISWIM pipeline]], counted as the four are but not (yet) in their comparison; its adequacy is reported separately. PR #50 was the pilot (ISWIM to Clos4, through delay). Since PR #53 its operators are built from an error monad on 𝒫 Value, with the graph model's operators as kernels; the counts before the monad are kept in [[#Before the monad]].

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

**The design** (`Framework/GraphModel/ErrorMonad.agda`, `Semantics/GraphErr/`; since PR #53 an error monad, see [[#Before the monad]]):

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

**Counts** (from `loc.py`; code lines; the four columns of [[#Counts of the ISWIM pipeline]]):

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

**Infrastructure** reached by each graph model: see the table under [[#Language-independent infrastructure]] above (the `both` column). The errors model now shares the graph model's operators (474 of their 623 lines: `Ops` and its proof half, `Continuity`, `DomainUtil`) as kernels, and adds 935 lines of its own (the monad, its operators and laws), against 1317 before. `loc.py` checks that it reaches no module of the other proofs except the graph model's meaning of the primitives and these operators, and prints the operator modules it reuses.

**What is still hard.**
* **Evaluation order.** Which operand errs first decides the result; the monad states it once (nesting of binds), but the relations of delay and adequacy still relate each error.
* **The early and the late operator check** are two operators, as in the machines.
* **Closed and well-scoped programs.** Simplify and enclose hold for closed programs, optimize and rco for well-scoped ones, because a free variable errs.
* **Inference.** Agda cannot infer a bind's continuation from an element of the bind (`≫=` unfolds under ∈), so each use of a bind lemma names it.

## Before the monad

PRs #50 and #51 built the graph model with errors with its own error-propagating operators (`ErrorOps`, `ErrorContinuity`, `ErrorStrict`, `ErrorLaws`: 1317 lines of infrastructure, none of the graph model's operators reused). Its counts: semantics and passes 3953 (delay 1037), adequacy 4760, infrastructure reached 2670. PR #53 rebuilt it on an error monad, first as a pilot beside it (ISWIM to Clos4, simplify, enclose, concretize, delay, ISWIM adequacy) and then for the whole column, which replaced it: passes and semantics 3528 (−11%), adequacy 4333 (−9%), error-specific infrastructure 935 (−29%), with the graph model's operators shared. The table above gives the old count of each row.

## Typed assembly language

*ISWIMμ:* X86μ (`Mu/Language/X86.agda`) is X86ᵀ with the types of CFGμ and no check: nothing traps, and a sum's `case` is one typed pseudo-instruction (no state type can give the payload's slot both the left and the right type between a load and a jump).

**Why.** From PR #56 to PR #58 the typed pipeline ended at untyped X86, so select had to show that its code never reaches one of X86's own trapped errors: an unset register, a missing label or definition, a missing flag, a slot beyond the frame, or an operand of the wrong kind. In the graph model with errors that could not even be an equation: X86's code tables give ω on ill-kinded inputs, where CFGᵀ checks only at `project`, so select was `Same`, through CFGᵀ with X86's checks added back and a 1015-line boundary (1349 lines in all, against 363 in the untyped pipeline). A pilot (PR #58, first commits) tried a typed assembly language as the target, X86ᵀ, after Morrisett, Walker, Crary and Glew's TAL and in the style of Rouvoet et al.'s intrinsically typed compilation to typed bytecode, in the CEK column and the graph model with errors: select there went from 482 to 228 lines (with `SelectFacts` and the target's machine) and from 1489 to 291, with select ≃. The user said go, and PR #58 made X86ᵀ the target in every column.

**Design** (`Language/Typed/X86.agda`, 98 lines against X86's 48).
* **Instructions are typed by machine states.** `Instr Σ n ψ ψ'` starts in a state of type ψ and leaves one of type ψ'; a state type gives the type of each register (or unset), the frame (a context Δ as in CFGᵀ: a slot is a typed index), the open closure, if any, and whether the flag is set. A slot write needs its level below the frame's n slots (an irrelevant argument). A label is a typed index into the frames the blocks expect.
* **Calls.** ⟪ fun ⟫ hides the length of a closure's environment, but `callq` needs code n with %rdi : ⟪ tup n ⟫. `load fst x, r` opens the closure in slot x (r : `codeα`), `load snd x, r` reads the environment of the open closure (r : `tupα`), and `callq` needs both; a slot write or a call closes the closure. Without the open closure in the state, `load snd` of any closure would type `callq`, unsoundly; recording it keeps the types first order.
* **The only check is `project`'s.** `chk t x, d` moves slot x : Any to d at ⟪ flat t ⟫ or stops with the error; it stands for X86's test of t and the move. Typing the test instructions themselves would need a singleton type linking %rax to x, or a refinement of the slot's type that CFGᵀ's frame disagrees with.
* **Select** (`Compiler/Select.agda`, 58 lines against 55) selects each simple expression in continuation-passing style, polymorphic in the registers, open closure and flag it starts with, so every register read is `refl`. Without the types it emits exactly the instructions of select into untyped X86 (see [[#Assurance]]).

**Findings.**
* **Select becomes small in every column**, since X86ᵀ holds the values of Clos5ᵀ in CFGᵀ's frame: no erasure of values, no agreement of frames at levels, no frame sizes, and no clause per wrong kind. Select with its target's semantics and `SelectFacts`, untyped X86 against X86ᵀ: graph model 366 → 199 (select 226 → 133, the semantics 103 → 66), CEK and reduction 482 → 225 (313 → 111, the machine and values 132 → 114), interpreter 341 → 162 (179 → 52, the interpreter and values 125 → 110), graph model with errors 1489 → 288 (1349 → 222, 103 → 66). The interpreter's proof needs no relation on values: the X86ᵀ program gives the CFGᵀ result for every clock.
* **Select is ≃ in both graph models**: most instructions mean the operator of the simple expression they compute, definitionally. What is left is the case (testinl, the payload into the slot and je take apart what CFGᵀ's case does at once, under an invariant that no slot holds both an inl and an inr), the call (CFGᵀ binds the closure and the argument first), and the start of a definition (a β on finite sets, by the monotonicity of CFGᵀ's semantics).
* **Register writes need no strictness.** The graph semantics write only `callq`'s and `chk`'s results strictly; every other instruction is total on operands of its type, so most instructions mean exactly CFGᵀ's operators. That this is faithful to the machine was argued in the pilot and is now proved by the direct X86ᵀ adequacy in both graph models.
* **Adequacy is direct** (internal information): a logical relation that follows the state types (graph model 679 + 41 for compiled programs, against 1240 for untyped X86; graph model with errors 1215 + about 50, against 2085), where the pilot had forecast deriving it from the CEK simulation in about 40 lines. Soundness still needs the finite approximations of the untyped proofs; what typing removes is the well-formedness of labels and slots and the cases for ill-kinded operands.
* **The cost** is in the shared rows (X86ᵀ +50 lines over X86, select +3), which no column counts, and in the audit surface, which reads a typed assembly language and its semantics instead of untyped X86's (graph model 1632 → 1649, CEK 1941 → 1977, interpreter 1625 → 1664, reduction 2112 → 2148, graph model with errors 2151 → 2196).
* **The totals**: graph model 2309 → 2131, CEK 2868 → 2648, interpreter 1960 → 1818, reduction 3836 → 3616, graph model with errors 3776 → 2614; adequacy 2980 → 2214 and 3540 → 2281.

## Typed intermediate languages (pilot, superseded)

*History.* This is the pilot that led to the typed pipeline (PR #55); the typed pipeline then became the main one (see [[#The ISWIM pipeline in full]] and [[#Typed against untyped]]; ISWIMμ has been the main experiment since), and the pilot's statements (`Theorems/Typed.agda`) and composition are retired. Its paths have changed (`Compiler/Typed/X` is `Compiler/X`, `proof/Correctness/Typed/<style>/X` is `proof/Correctness/<style>/X`); its findings stand. Two of its design points changed in phase 1 (PR #56): a Clos4ᵀ closure is eliminated by `callc`, the parametric elimination, not by `unpack` with a family of bodies, which cannot be compiled to untyped code (delay in the graph model with errors, 878 lines in the pilot, is 801 now); and `project` takes a `Tag`, the flat types an X86 instruction can test. **Outcome of its forecast** (below): globalize shrank in the graph models (155 → 118, 157 → 105) but grew in the operational ones (CEK 157 → 219); rco shrank most in the CEK column (396 → 150), as forecast; lift locals and explicate control shrank in every column; select grew in every column, most in the graph model with errors (363 → 1349, the typed/untyped boundary); X86 adequacy is unchanged, and Clos5ᵀ adequacy in the graph model with errors is derived from the CEK column rather than proved by a logical relation of its own.

Not in the totals (when it was written). Then ISWIM and every intermediate language are untyped. Each semantics checks the kinds of values itself, and a misuse stops with the trapped error `o-error` / ω. The pilot asks whether that error handling goes away when casts are inserted early, as in *Essentials of Compilation*, ch. 9, so that the intermediate languages are statically typed. It covers ISWIM → Clos4 in two contrasting columns, the CEK machines and the graph model with errors. Its statements are in `agda/Theorems/Typed.agda`.

    ISWIM --cast insertion--> ISWIMᵀ --enclose--> Clos2ᵀ --optimize--> Clos2ᵀ --concretize--> Clos3ᵀ --delay--> Clos4ᵀ

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
  * Optimize (`Compiler/Typed/Optimize.agda`, 67 lines) prunes a closure's free variables as the untyped pass does: it drops one that the code does not use and whose term is a variable (closures are strict), and renames the code's variables. Its Bool-valued `uses` (17 lines) and the facts both proofs share about the kept positions (22) are in the pass module; the selection of kept positions is infrastructure (`Framework/VecSelect.agda`).
  * Delay is `app L M ⇒ unpack L' (λ n → call (` 1) (` 0) M')`, with a renaming for the two variables.
* **CEK machines** (`Semantics/CEK/Typed/`). Values, environments and continuations are typed, and a state is well typed by construction. Each machine has one way to stop with `o-error`, a failed project. The untyped machines have five or six, plus an unbound variable.
* **Graph model with errors** (`Semantics/GraphErr/Typed/`).
  * The operators are the graph model's under the binds of the error monad, with no `checked`.
  * `inject` is the identity, since a value's kind is its tag.
  * `project k D = D ≫= λ X → checked k X (X ⇂ kind ≡ k)`. It keeps only the values of the right kind; without that filter a denotation is not consistent.
  * In Clos4ᵀ a function is a pair. Its project sees kinds through `kind₄`, which maps a pair to a function (`checkedᵠ`, infrastructure), so that every language projects to the same kind `kindᶠ G` and a Clos4ᵀ closure has the kind of a function.
  * `unpack` runs its body for the length n of the environment, read off the kind `tup n` of its values. Running it for every n would give `const n` for every n in a body that ignores its environment.

The pilot's proof agents found these last three points: their first versions were wrong.

**Counts** (from `loc.py` as of PR #55, which no longer prints this table; code lines). The rows of "today" are those of the same segment in [[#Counts of the ISWIM pipeline]]. The languages, passes and semantics rows count only ISWIM–Clos4; the passes are shared by both columns. In each column the lower of today and typed is bold.

| typed pilot, ISWIM → Clos4 (not in the totals) | CEK machine + simulation: today | CEK machine + simulation: typed | graph model with errors: today | graph model with errors: typed |
|---|---:|---:|---:|---:|
| languages ISWIM–Clos4 (shared) | 115 | **101** | 115 | **101** |
| passes (shared): cast insertion | — | 26 | — | 26 |
| passes (shared): CC: enclose, concretize, delay | 89 | **79** | 89 | **79** |
| passes (shared): CC: optimize | **55** | 67 | **55** | 67 |
| passes (shared): the compiler | — | 3 | — | 3 |
| semantics of the languages | 324 | **322** | 215 | **174** |
| lemmas shared by the passes | — | 30 | — | — |
| cast insertion | — | 195 | — | 122 |
| CC: enclose | 188 | **106** | 90 | **38** |
| CC: optimize | 224 | **133** | 149 | **63** |
| CC: concretize | 182 | **115** | 134 | **69** |
| CC: delay | 134 | **101** | 898 | **878** |
| composition | — | 5 | — | 17 |
| **total** | 1311 | **1283** | 1745 | **1637** |
| **total without cast insertion (like for like)** | 1311 | **1062** | 1745 | **1489** |

| typed pilot: infrastructure (not in the totals) | lines | used by typed CEK | used by typed graph model with errors |
|---|---:|---:|---:|
| decidable base types, vectors (collecting, selecting) | 89 | 89 | 79 |
| semantics of intrinsically typed syntax (graph model) | 201 | — | 201 |

* **The CC passes shrink in both columns.**
  * **CEK:**
    * enclose 188 → 106;
    * optimize 224 → 133;
    * concretize 182 → 115;
    * delay 134 → 101.
  * **Graph model with errors:**
    * enclose 90 → 38;
    * optimize 149 → 63;
    * concretize 134 → 69;
    * delay 898 → 878.
* **Cast insertion is new**, and it is where the kind errors are now handled: CEK 195 (147 for the simulation, plus 48 lines of list and primitive lemmas copied from adequacy so that the pilot does not import it), graph model with errors 122.
* **The segment.**
  * Counting cast insertion: CEK 1283 against 1311, graph model with errors 1637 against 1745.
  * Like for like, leaving cast insertion out of both sides (see the recommendation: the late design must insert the checks too): CEK 1062 against 1311 (−19%), graph model with errors 1489 against 1745 (−15%).
* **The typed CEK machines are no shorter** (322 against 324). The kind cases are gone, but typed continuations, the length equations of tuple frames (`Framework/VecUtil.agda`, infrastructure) and inject/project frames take their place.
* **The typed graph semantics (174) are 104 lines of definitions and 70 lines of lemmas.**
  * The untyped semantics get monotonicity, consistency and continuity from the generic fold over abstract binding trees (`GoodSemantics`, infrastructure).
  * The typed semantics are defined by recursion on intrinsically typed terms, so they need the same facts. Infrastructure for semantics of intrinsically typed syntax (`proof/Framework/GraphModel/{TypedOk,TypedBinders}.agda`, `Framework/GraphModel/TypedCheck.agda`, 201 lines) now gives them from per-operator properties:
    * `Ok` (monotone, consistent, continuous) and its combinators for an operator, a variable, a constant, a let, a vector of operands, code, and the existential `unpack`;
    * the β laws of code, and the finitary bodies the β laws need.
  * What stays in the column is per-operator facts (Clos2ᵀ, 26 lines: each typed operator is `Good`, and its congruence) and, per language, the structural induction `ok`, one line per constructor, with `oks` and `con` (Clos3ᵀ 22, Clos4ᵀ 22).
  * Before that infrastructure these lemmas were 266 lines. A generic fold proper, as for the abstract binding trees, would need the typed languages to be instances of one generic syntax. Each language would then need a description, a translation into it and a proof that it agrees with the semantics, which costs more than the one-line-per-constructor induction it replaces.
* **The audit surface of the pilot:** 812 lines of its own (types, languages, passes, semantics, statements), against 115 lines of languages, 144 of passes and the semantics rows today.

**Error handling removed.**
* **CEK.**
  * The untyped enclose, concretize and delay spend 15, 15 and 11 clauses on a value of the wrong kind (`stops refl`). Untyped delay also needs a state for the early operator check (`retT`, `ret-reach`).
  * Untyped enclose carries the scoping bookkeeping of free variables (`Agree`, `Lookup` with `Maybe`, `bound`).
  * The typed proofs have none of these: the coverage checker rules the cases out.
  * What is left of errors is 6 lines per proof for project, a step that succeeds or stops in both machines, plus 7 shared lines (`Lock`).
  * Cast insertion spends about 28 of its 147 lines on errors.
* **Graph model with errors.**
  * Enclose, optimize and concretize handle errors with one congruence line each for `project`; that `project` is `Good` is one line on infrastructure.
  * In cast insertion, about 81 of 122 lines relate a check to a project.
  * Delay is the exception (below).
* **The early and the late operator check** are gone. ISWIMᵀ to Clos3ᵀ application and Clos4ᵀ's call check nothing, because cast insertion has already put the operator's project where the ISWIM machine checks it. Typed CEK delay is a plain plus simulation.

**Why typed delay in the graph model is hardly smaller** (878 against 898; 594 in the graph model without errors). The types did remove the early and late checks, the let through Λ, and the checks of prim, get and case: the backward fundamental lemma went from 376 to 333. Three costs come back.
* **The relation cannot be indexed by types.** `Any` contains `⟪ fun ⟫`, so the types are recursive. The forward relation still recurses on source values. The backward relation is still indexed by the depth of finite target lists. A closure's calls still mix the code and environments of several pairs (`Calls`, `collect`).
* **Project's filter** relates sets restricted by kind on both sides (about 80 lines with its error).
* **Others:**
  * a typing invariant that a value of type `⟪ fun ⟫` is a function (25 lines);
  * the renamings of typed delay (about 35);
  * the semantic lemmas above.

  Giving a Clos4ᵀ closure the kind of a function (its project sees a pair as a function) saved 41 lines of delay (919 → 878): the kind correspondence between the two languages (`tgt`, `back`, `isfun`, the `≢ prod` side conditions) is gone, for 4 more lines of the semantics and 12 of infrastructure.

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

**Recommendation: go — insert the checks early.**
* **The question is where the checks go, not whether.** Today's pipeline never makes the kind checks explicit: every semantics down to X86 checks kinds itself. A compiler to real x86 has to insert them somewhere, as tag tests on tagged words. Cast insertion is that pass, put early. It extends the compiler towards a complete one; that the later passes get simpler is a bonus.
* **So the like-for-like comparison leaves cast insertion out of both sides.** The late design would need its own check-insertion pass (near select, as *Essentials of Compilation*'s `reveal_casts` and tag bits are), whose proof relates each implicit check to tag-test code. It is not measured, but at that level it is unlikely to be cheaper than cast insertion's 195 / 122 lines.
* **On that basis, early wins in the passes:**
  * CEK: the CC proofs (enclose, optimize, concretize, delay, plus 30 shared lines) are 485 against 728;
  * graph model with errors: 1048 against 1271;
  * the segment, with the languages, passes and semantics: CEK 1062 against 1311, graph model with errors 1489 against 1745.
* **The semantics cost nothing more.** Typed CEK machines are no shorter (322 against 324). The typed graph semantics are 174 against 215, now that their monotonicity, consistency and continuity come from infrastructure for intrinsically typed syntax (201 lines, not counted, as the untyped fold is not).
* **The later passes should gain more** (rco, lift locals, explicate control, globalize), and select would carry the remaining invariant that X86's own trapped errors are unreachable.
* **Done since the first pilot:** optimize for the typed languages, the infrastructure for typed semantics, and the function kind for Clos4ᵀ closures.
