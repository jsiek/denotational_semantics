# Size of the two compiler-correctness proofs

Both proofs establish end-to-end correctness for the same compiler, `compile`, which runs
ISWIM --enclose--> Clos2 --optimize--> Clos2 --concretize--> Clos3 --delay--> Clos4 --globalize--> Clos5.

* **Denotational:** a graph-model semantics for each language and one correctness proof per pass, in `agda/Compiler/Model/Graph/`. The theorem is `CompilerCorrect`: the source and compiled program produce the same constants, and one denotation is nonempty exactly when the other is.
* **Operational, CompCert style:** a small-step CEK machine for each language and one forward simulation per pass, in `agda/Compiler/Operational/`. The theorem is `CompilerSim`: the two programs terminate with the same observation, including going wrong, and one diverges exactly when the other does.

Counts are code lines: lines that are neither blank nor comments. The table is regenerated with
`python3 papers/PLDI-2027/loc.py` from the repository root. The script fails if any Agda module is not assigned to a group.

## Current counts

As of this PR:

| component | denotational | operational |
|---|---:|---:|
| generic infrastructure | 303 | 357 |
| domain, operators, continuity | 465 | — |
| semantics of the languages | 458 | 469 |
| enclose | 110 | 236 |
| optimize | 152 | 345 |
| concretize | 234 | 235 |
| delay | 813 | 218 |
| globalize | 234 | 240 |
| composition | 56 | 34 |
| **total** | **2825** | **2134** |

Adequacy relates the denotational semantics of ISWIM and Clos5 to their machines. It turns `CompilerCorrect` into a statement about running programs (`Adequacy/EndToEnd.agda`). It is reported separately, because the denotational semantics can be taken as *the* semantics of a language, in which case adequacy is not needed.

| adequacy (denotational side only) | lines |
|---|---:|
| ISWIM | 757 |
| Clos5 | 941 |
| well-formedness of compiled programs | 289 |
| end to end | 24 |
| **total** | **2011** |

Not counted: code that both proofs use (791 lines: syntax, languages, compiler passes) and examples (185 lines).

## What the groups contain

* **generic infrastructure:**
  * denotational: sets as predicates, environments, generic semantics, monotonicity and continuity over operator signatures;
  * operational: observations, small-step transition systems, forward simulation, and the iff end theorem.
* **domain, operators, continuity:** the graph-model values, consistency, the semantic operators and their monotonicity, consistency and continuity lemmas.
* **semantics of the languages:**
  * denotational: the semantics of ISWIM and Clos2 through Clos5, plus the continuity instances the proofs use;
  * operational: the six machines.
* **one row per pass:** that pass's correctness proof.
* **composition:** the end-to-end theorem built from the per-pass results.

## Caveats

* **The two theorems differ.** The operational theorem is stronger: it separates going wrong from divergence. In the graph model, both denote ∅.
* **Determinism.** The operational proof relies on every machine being deterministic and total. The backward direction of each pass comes from forward simulation plus determinism, and the framework proves that once.
* **Machines.** The machines check that an operator is a function before evaluating the argument. Delay needs this to preserve going wrong.

## History

| date | change | denotational | operational |
|---|---|---:|---:|
| 2026-10-11 | first complete versions (PR #14) | 4251 | 2134 |
| 2026-10-11 | leaner delay proof (PR #15) | 3725 | 2134 |
| 2026-10-11 | dead code, consistency, shared lemmas (PR #16) | 2836 | 2134 |
| 2026-10-11 | delay relation without visible fuel, Calls as a predicate (this PR) | 2825 | 2134 |

PR #16 also changed the grouping: the shared counts now include `Primitives`, `NewSigUtil` and `NewSyntaxUtil`, and `ISWIMContinuous` moved to adequacy. Earlier rows used slightly different groups, so they are only roughly comparable.

## Why delay costs more on the denotational side

As of this PR; the denotational proof is 813 lines and the operational one 218.

**Denotational** (`Correctness/Delay*.agda`):

| part | lines | what it is |
|---|---:|---|
| **backward direction (reflect)** | **≈ 494** | |
| – finite-observation machinery | 193 | the relation R with the call batches (128), depth and `Bnd` (27), `collect` (38), which extracts finite witnesses of a target call |
| – fundamental lemma | 194 | one case per construct, plus helpers for nonemptiness, tags, pairs and case branches |
| – semantic side conditions | 48 | consistency of Clos4 terms (16); a source β-law and a "one finite part of the bound variable suffices" lemma (32) |
| – imports and end theorem | 43 | |
| **forward direction (preserve)** | **≈ 210** | |
| – the relation ⊑ and its lemmas | 46 | |
| – target laws | 41 | a β-law for closures, `case` contains its branch, one finite part suffices |
| – fundamental lemma | 78 | |
| – imports and end theorem | 45 | |
| **shared** | **≈ 110** | |
| – the `let`/`fst`/`snd` application equation | 45 | `DelayApp` |
| – shorthands, list helpers, flat values | 62 | |

**Operational** (`Correctness/DelaySim.agda`):

| part | lines |
|---|---:|
| renaming lemmas, generic over any syntax | 62 |
| relations: values, terms, environments, continuations; the run-ahead state | 58 |
| the simulation, all cases | 66 |
| end theorems (40% are corollaries) | 21 |
| imports | 11 |

**Where the ≈ 3.7× comes from:**

1. **Two directions instead of one: about 494 lines.** Delay changes how functions are represented, so the result is not an equation, and preserve and reflect need different relations. Operationally, the backward direction comes from forward simulation plus determinism. The generic framework proves that once, and it is counted there. Preserve alone plus the shared part is about 320 lines, roughly 1.5× `DelaySim`.
2. **Finite observations in reflect: about 193 lines, plus part of the app case.** A target call takes its code from `car C` and its free variables from `cdr C` separately. A single target value says nothing about a call, so the relation ranges over finite lists, with batches and a depth index. Joined pairs (a pair as one value) were tried and do not change this.
3. **β needs side conditions: about 130 lines.** In the graph model, β for closures, `let` and `case` holds only with nonemptiness and continuity. That costs `clos-β` and `cont-0` on both sides, the application equation, and consistency for `case`. Operationally, β is a machine step.
4. **Imports: 82 lines against 11.**
5. **Per-construct cases are comparable once the plumbing is gone.** Preserve's fundamental lemma is 78 lines against 66 for the simulation cases.

The cost is not in the compositional, per-construct reasoning. It is in the backward direction forced by the change of representation (item 1), and in the side conditions β needs in the graph model (item 3). Operational proofs pay for the backward direction once, through determinism. The denotational proof pays for it in each pass that is not an equation, and delay is the only such pass.
