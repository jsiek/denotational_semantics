# Paper outline (draft 2)

Title: TBD. The working title "There is no semantics to rule them all!" fitted a comparison paper and will change.

This is an outline for discussion, not paper text. Numbers come from `loc.py --mu` on master after PR #66 and will change. Paper sections are written double-blind: earlier work in this repository is "we", without saying who (see `history-outline.md`).

## Main claim
A denotational semantics based on graph models can be used to prove a realistic compiler correct, mechanized, all the way to assembly. The compiler goes from ISWIMμ (a call-by-value λ-calculus with recursive types) to a typed x86 in ten passes. Each pass is proved by relating denotations, and adequacy connects the result to running code. The novelty claims are pending the literature check (`novelty-lit.md`, to be added to the notes).

## Research questions
- **RQ1. Can a graph-model semantics be used to prove the correctness of a compiler?** Mechanized, through closure conversion, down to assembly, with an end-to-end theorem about running code.
- **RQ2. What does it take?** Which passes are equations, what needs a relation (the approximant logical relation), the supporting properties of the model (consistency, continuity), and adequacy at both ends.
- **RQ3. How does it compare with the operational approaches on the same compiler?** The operational proofs are experimental setup, not contributions: they give an apples-to-apples baseline.
- **RQ4 (brief). How do dynamic typing and errors affect this?**

## 1. Introduction
- **Motivation.** Denotational semantics promises compositional, equational reasoning about programs, yet mechanized compiler verification has been operational, with CompCert's simulations as the standard. Graph models are an elementary, set-theoretic form of denotational semantics (Plotkin, Scott, Engeler) that is easy to mechanize, but they have been used for little beyond adequacy and source-level optimizations.
- **What we did (RQ1).** We proved a ten-pass compiler correct with graph-model semantics for every intermediate language, ending in an end-to-end theorem: the source and the compiled x86 program stop with the same constant, or both diverge.
- **What it took (RQ2).**
  - Most passes are equations of denotations, proved one construct at a time.
  - Closure lowering (delay) needs a new kind of relation for its reflection direction: the approximant logical relation.
- **How it compares (RQ3).** We proved the same compiler in three operational styles under the same accounting rules:
  - totals: graph 1958, CEK 2258, interpreter 1653, reduction 3207;
  - the graph model is smallest for equational passes (simplify 360 against 584–715);
  - it is costliest for delay (524 against 35–139).
- **Contributions:**
  1. a mechanized graph-model correctness proof of a realistic compiler, down to a typed assembly language, with adequacy at both ends;
  2. the approximant logical relation, for passes that lower abstraction;
  3. a like-for-like measurement against three operational styles on the same compiler, pass by pass;
  4. the effect of dynamic typing and errors (brief).

## 2. Background: graph models
- **Denotations.** A denotation is a set of finite values. A function's finite value is a finite table of input/output entries, and application ⟦L M⟧ρ collects the outputs of the tables in ⟦L⟧ρ whose inputs are covered by ⟦M⟧ρ.
- **The properties the proofs rely on:**
  - monotonicity and continuity;
  - consistency, with binders that bind only consistent finite sets;
  - divergence denotes ∅.
- **Why reflection is the hard direction.** Divergence is the absence of elements, so a forward relation cannot carry it. A correctness statement ⟦src⟧ ≃ ⟦tgt⟧ therefore needs both inclusions.

## 3. The compiler
- **ISWIMμ:** integers, tuples, sums, primitives, and iso-recursive types with `fold`/`unfold`. There is no `fix`: recursion and divergence come from the Z combinator, typed through μ.
- **The pipeline:**
  - simplify (a simplified cp0);
  - closure conversion in four passes: enclose, optimize, concretize, delay;
  - globalize, remove complex operands, lift locals, explicate control, select instructions;
  - the target X86μ, a typed assembly language.
- **Intrinsically typed intermediate languages:** no pass needs a scoping or typing precondition.
- Fig. 1: the pipeline.

## 4. Proving the compiler correct with graph models (RQ1, RQ2)
- **4.1 The semantics** of each intermediate language as a graph model. Closures, code tables, frames and control-flow graphs all get graph-model meanings.
- **4.2 Equational passes.** For simplify, enclose, optimize, concretize, globalize, rco, lift locals and explicate, ⟦pass M⟧ ≃ ⟦M⟧ is proved construct by construct from operator laws. Typical shapes and sizes.
- **4.3 Delay and the approximant logical relation** (the technical core):
  - **the problem:** a target call takes its code from `car` and its environment from `cdr` separately;
  - **why the natural relations fail** (`history-outline.md`): single values; whole sets (▷ with nothing to discharge it); element depth (as in Pitts's projections); one target point in an infinite context;
  - **the insight:** only one side needs to shrink, and the car/cdr matching happens inside the index;
  - **the definition:** 𝖠𝖫𝖱(D, V′), its layers, fuel as a termination device, depth irrelevance;
  - **why a type index cannot replace the depth index:** at μX. X ⇒ Int the application case returns to the same type.
- **4.4 Select and the typed assembly language.** The meaning of X86μ, and select proved as an equation.
- **4.5 Adequacy and the end-to-end theorem:**
  - adequacy for ISWIMμ against its abstract machine, and for X86μ directly;
  - no-error lemmas;
  - the end theorem, the same one the operational proofs state.
- **4.6 Mechanization.** Agda (`--safe`, stdlib only), the audit surface, sizes.

## 5. Evaluation: comparison with operational approaches (RQ3)
- **Setup.** The same compiler proved with CEK machines and simulations, clocked interpreters with value relations, and reduction semantics with simulations, each a best effort. These are the baseline, not contributions.
- **Accounting rules:**
  - semantics, per-pass proofs and compositions are counted;
  - infrastructure is counted by use and reported separately;
  - imports are not counted;
  - adequacy is reported separately.
- **Table 1, the main per-pass comparison:**
  - totals: graph 1958, CEK 2258, interpreter **1653**, reduction 3207;
  - graph wins simplify, globalize and explicate; the interpreter wins most of the rest;
  - without delay, graph would be smallest: 1434 against 1618.
- **Analysis by kind of pass:**
  - equational passes are cheap denotationally;
  - passes that change how values are represented need a relation in every style, but only the denotational proof must also reflect divergence;
  - machine states and administrative steps cost the CEK and reduction styles.
- **Full cost:**
  - semantics rows: reduction's semantics are the largest;
  - infrastructure: graph 1542, CEK 447, interpreter 413, reduction 1190;
  - adequacy, which only the denotational route needs: 1599 lines;
  - the audit surface.
- **Threats to validity:**
  - lines of Agda as a proxy for effort;
  - effort and expertise per style;
  - AI assistance, with an ACM disclosure;
  - what infrastructure each style could share.

## 6. Dynamic typing and errors (RQ4, brief)
- **The same compiler from dynamically typed ISWIM:** cast insertion, `Any = μX. Σ_G G[X]`, `project`/`chk`, and a graph model with errors to observe them.
- **Totals barely move:** graph 2064 → 1958, CEK 2390 → 2258, interpreter 1719 → 1653, reduction 3320 → 3207.
- **Delay's cost comes from recursive types, not errors:** graph delay goes 552 → 524 (errors account for about 28 lines).

## 7. Discussion: mixing semantics
- Graph models are cheapest for equational passes, and the operational styles for passes that change representation. A compiler proof could use a different style for each pass, joined where needed by adequacy or by a simulation between styles.
- What it would cost, and what the end theorem would be. This is worth exploring; it may become an experiment that reports numbers, not just a discussion point.

## 8. Related work
Organised as in `related-work-literature.md` and the novelty search:
- **Denotational compiler verification:** Chlipala 2007, Benton–Hur, interaction trees and Vellvm, calculated compilers (Hutton–Bahr), and earlier work (Morris, Thatcher–Wagner–Wright, Wand, Clinger, Polak).
- **Graph and filter models, and their mechanizations:** Plotkin, Scott, Engeler, and Siek 2017 and PLFA (cited in the third person).
- **Relations for adequacy versus relations between two denotations:** Reynolds 1974 (the tower), Pitts, Milne–Strachey, Stoy, Mulmuley.
- **Operational compiler verification:** CompCert, CakeML, Hur–Dreyer, typed closure conversion.

## 9. Conclusion and future work
- Graph models work for compiler verification. They are cheapest where passes are equations, and their cost concentrates in passes that lower abstraction.
- Future work:
  - mixing semantics;
  - a generic framework for intrinsically typed syntax;
  - effects (exceptions, call/cc);
  - exposing allocation.

## Figures and tables
- Fig. 1: the pipeline.
- Fig. 2: graph-model semantics of a few constructs.
- Fig. 3: the approximant logical relation.
- Table 1: per-pass sizes in the four styles.
- Table 2: dynamic typing and errors.
- Table 3, possibly: infrastructure, adequacy and the audit surface.

## Open questions
- The title.
- Novelty claims, to be worded after the literature check.
- The page budget for §4.3 against §5.
- Whether mixing semantics (§7) becomes an experiment before submission.
- Matthew Heimerdinger's affiliation.
- The artifact: an anonymized copy of the Agda development.
