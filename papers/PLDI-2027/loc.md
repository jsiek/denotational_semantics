# Size of the two compiler-correctness proofs

Both proofs establish end-to-end correctness for the same compiler, `compile`, which runs
ISWIM --enclose--> Clos2 --optimize--> Clos2 --concretize--> Clos3 --delay--> Clos4 --globalize--> Clos5.

* **Denotational:** a graph-model semantics for each language and one correctness proof per pass, in `agda/Compiler/Model/Graph/`. The theorem is `CompilerCorrect`: the source and compiled program produce the same constants, and one denotation is nonempty exactly when the other is.
* **Operational, CompCert style:** a small-step CEK machine for each language and one forward simulation per pass, in `agda/Compiler/Operational/`. The theorem is `CompilerSim`: the two programs terminate with the same observation, including going wrong, and one diverges exactly when the other does.

Counts are code lines: lines that are neither blank nor comments. The table is regenerated with
`python3 papers/PLDI-2027/loc.py` from the repository root. The script fails if any Agda module is not assigned to a group.

## Current counts

As of master `da7689a`:

| component | denotational | operational |
|---|---:|---:|
| generic infrastructure | 303 | 357 |
| domain, operators, continuity | 465 | — |
| semantics of the languages | 458 | 469 |
| enclose | 110 | 236 |
| optimize | 152 | 345 |
| concretize | 234 | 235 |
| delay | 824 | 218 |
| globalize | 234 | 240 |
| composition | 56 | 34 |
| **total** | **2836** | **2134** |

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

PR #16 also changed the grouping: the shared counts now include `Primitives`, `NewSigUtil` and `NewSyntaxUtil`, and `ISWIMContinuous` moved to adequacy. Earlier rows used slightly different groups, so they are only roughly comparable.
