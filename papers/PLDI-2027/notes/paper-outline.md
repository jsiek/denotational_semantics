# Paper outline (draft)

Working title: **There is no semantics to rule them all!**

A first outline for discussion, not paper text. Numbers are from `loc.py --mu` on master after PR #66 and will change. Paper sections are written double-blind: earlier work in this repository is described as "we", without saying who (see `history-outline.md`).

## Thesis
One compiler, from a typed ISWIM with recursive types to a typed x86, is proved correct four times, once per semantic style: a denotational graph model, a CEK machine with simulations, a clocked interpreter with value relations, and a reduction semantics with simulations. Each style was given a best effort, under the same accounting rules. No style is smallest for every pass. The cost of a proof depends on how well the pass's change of representation fits the style. The clearest example is closure conversion's delay pass, which is cheap operationally and expensive denotationally. It needed a new kind of logical relation, the approximant logical relation.

## 1. Introduction
- The question: which semantics makes compiler correctness proofs smallest? Folklore favours operational semantics with simulations (CompCert); denotational semantics promises compositional, equational proofs.
- What we did: the same compiler, the same proof obligations, four styles, mechanized in Agda (`--safe`, stdlib only), with a fair line count.
- Headline results (main table, §5):
  - totals: graph 1958, CEK 2258, interpreter **1653**, reduction 3207;
  - per pass, the smallest style varies: graph wins simplify (360 against 584–715), globalize and explicate; the interpreter wins most of the others;
  - delay is the outlier: graph 524 against interpreter 35. Without delay, graph would be smallest (1434 against 1618).
- Contributions:
  1. the four mechanized proofs and the accounting method;
  2. the approximant logical relation, for reflecting a pass that lowers abstraction between two graph-model semantics;
  3. a per-pass analysis of which style suits which kind of pass;
  4. the effect of dynamic typing and errors (brief): it changes totals by 1–7% and does not change the ranking.

## 2. The compiler
- ISWIMμ: call-by-value λ-calculus with integers, tuples, sums, primitives and iso-recursive types (`fold`/`unfold`). There is no `fix`; recursion and divergence come from the Z combinator, typed through μ.
- The pipeline:
  - simplify (a simplified cp0);
  - closure conversion in four passes: enclose, optimize, concretize, delay;
  - globalize, rco, lift locals, explicate control, select;
  - the target X86μ, a typed assembly language.
- All languages are intrinsically typed, so no pass needs a scoping or typing precondition.
- One figure: the pipeline with each language's key feature.

## 3. Four semantics
For each style: what a semantics of each language looks like, and the shape of a pass-correctness proof.
- **Graph model:** a denotation is a set of finite values (Plotkin/Engeler style), and a correctness statement is ⟦src⟧ ≃ ⟦tgt⟧. Adequacy connects it to running code and is reported separately.
- **CEK machine + forward simulation:** a generic simulation framework; backward simulation from forward simulation plus determinism.
- **Clocked interpreter + value relations:** proofs that go clock for clock.
- **Reduction semantics + simulation:** substitution by the standard kit; explicate and select reuse the CEK machines.
- The common end-to-end theorem, for `main : Int`: the source and the compiled X86 program stop with the same constant, or both diverge.
- **Fairness and accounting:**
  - best effort in every style;
  - what counts: semantics, per-pass proofs, compositions;
  - what doesn't count: infrastructure is counted only by use and reported separately; imports aren't counted; adequacy is reported separately;
  - the audit surface (the theorem statements and the definitions they use).

## 4. The approximant logical relation
- **The problem:** reflecting delay (closure lowering) in the graph model, ⟦tgt⟧ ⊆ ⟦src⟧. A target call takes its code from `car` and its environment from `cdr` separately.
- **A tour of the natural relations and why each fails** (`history-outline.md`):
  - single values;
  - whole sets, needing ▷ with nothing to discharge it;
  - element depth, as in Pitts's projections;
  - one target point in an infinite target context.
- **The insight:** a simulation needs only one side to shrink, and the car/cdr matching must happen inside the index. So the relation pairs a finite target approximant with an arbitrary source set, by recursion on the approximant's depth.
- **The definition:** 𝖠𝖫𝖱(D, V′) and its layers, fuel as a termination device, depth irrelevance.
- **Why a type index can't replace the depth index:** at μX. X ⇒ Int the application case returns to the same type.
- **Cost:** delay in the graph model is 524 lines, mostly the relation and reflection.

## 5. Results
- **The main table:** rows are semantics, simplify, each pass and composition; columns are the four styles; lowest number bold. Plus infrastructure by use, adequacy, and the audit surface.
- **Per pass:**
  - which representation changes suit which style;
  - equational passes (where ⟦pass M⟧ ≃ ⟦M⟧) are cheap denotationally;
  - passes that change how values are represented need a relation in every style, and only the denotational one must also reflect divergence (∅);
  - CEK and reduction pay for machine states and administrative steps;
  - the interpreter is cheapest wherever a pass is a local rewrite.
- **Semantics rows:** what each style must define, and why reduction's semantics are the largest.
- **Infrastructure:** graph 1542, CEK 447, interpreter 413, reduction 1190 (not in the totals). Discuss what is reusable.

## 6. Dynamic typing and errors (brief)
- The same compiler from dynamically typed ISWIM: cast insertion, `Any`, `project` and `chk`, and a fifth column, the graph model with errors.
- **Totals barely move** (typed ISWIM without cast insertion → ISWIMμ): graph 2064 → 1958, CEK 2390 → 2258, interpreter 1719 → 1653, reduction 3320 → 3207. The ranking is unchanged.
- **Delay's cost is caused by recursive types, not by errors:** 552 → 524 lines. Errors account for about 28 lines (`fun-obs`, the `project` cases).
- `Any = μX. Σ_G G[X]`: the ISWIM pipeline is ISWIMμ plus an error construct.
- The graph model with errors: what observing errors costs in the denotational style.

## 7. Related work
Organised as in `related-work-literature.md`:
- relations for adequacy: Martin-Löf, Winskel §13.4, Abramsky, intersection types, and Siek 2017 and PLFA (cited in the third person);
- relations between two denotational semantics: Reynolds 1974 (the tower's shape), Milne–Strachey, Stoy, Mulmuley, Pitts, Meyer–Wand, Filinski, and Chlipala 2007 (closest in purpose);
- compiler verification: CompCert and its simulation style, CakeML, Benton–Hur, Hur–Dreyer, Minamide–Morrisett–Harper, and the Wand–Clinger single-model approach;
- comparisons of semantic styles and of proof effort.

## 8. Conclusion
- No style rules them all; the right choice is per pass.
- Consequences: mix styles across passes (adequacy and simulation can be composed), or pick a style that suits the passes that change representation most.
- Future work: a generic framework for intrinsically typed syntax, which would remove per-language Ok and renaming lemmas; exceptions or call/cc; exposing allocation.

## Figures and tables
- Fig. 1: the pipeline.
- Fig. 2: the four semantics of one construct, e.g. application.
- Fig. 3: the approximant logical relation.
- Table 1: the main per-pass comparison.
- Table 2: dynamic typing and errors (typed ISWIM vs ISWIMμ per style).
- Table 3, possibly: infrastructure and the audit surface.

## Open questions for the author
- The page budget for §4 against §5: the relation is a contribution in its own right, but the comparison is the main story.
- Whether to present adequacy sizes at all (currently internal).
- Whether the CompCert-style framing belongs in the introduction or only in related work.
- The artifact: an anonymized copy of the Agda development.
