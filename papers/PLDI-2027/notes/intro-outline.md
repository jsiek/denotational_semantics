# Outline of the revised introduction

Follows the order of abstract-v2.tex. One bullet per paragraph. Numbers
checked against Table 1 and Table 2 of evaluation.tex on 2026-10-31.

1. **Punch lines and road map.** First denotational proofs that closure
   conversion preserves and reflects meaning (divergence included) for a
   Turing-complete language, in a graph model and in Scott domains,
   extended to an eight-pass compiler and mechanized in Agda. Comparing
   with three operational proofs of the same compiler, no style is
   smallest for every pass; the interpreter proof is smallest overall
   (1,504 lines) and the graph-model proof second (1,808). Denotational
   proofs are short when correctness is an equation between meanings and
   long when a pass needs a logical relation; operational proofs grow
   with how much the runs of source and target differ. One-sentence road
   map (replaces the closing road-map paragraph).
2. **Choosing a semantics.** CompCert (simulations), CakeML (induction on
   evaluation of clocked interpreters). The crisp recipe of denotational
   semantics; Polak, Clinger. We ask whether it works, and at what cost.
3. **The obstacle: closure conversion.** Every compiler for lexically
   scoped functions performs it; it turns functions into data. Prior work
   grouped by why it stops short, keeping the quotations: Chlipala 2007
   (no recursion), Nielsen (preservation only; quote), Banerjee et al.
   (operational source; quote), first-order compilers (Polak, Xia et al.,
   Cheng et al.), targets with closures (Clinger, Benton et al.), and
   Chlipala 2010 switching to operational semantics (quote). Bold claim:
   no denotational proof covers closure conversion for a Turing-complete
   language.
4. **Preservation and reflection; why reflection is hard.** Negative
   self-reference over a recursive domain; in the graph model, code-
   environment combinations that correspond to no source function.
5. **Research questions** (proposed, three):
   - RQ1 feasibility: can a denotational semantics prove a compiler
     correct through closure conversion, preserving and reflecting
     meaning, for a Turing-complete language? Yes, in two models (§4).
   - RQ2 comparison: how do proof sizes compare across the five styles,
     per pass and overall? No style wins every pass (§5).
   - RQ3 explanation: which properties of a pass determine proof size in
     each style? Equation vs. logical relation; difference between runs
     (§4.1, §5.3).
6. **Our two closure-conversion proofs.** Approximant logical relation
   (finite set of target elements vs. whole source denotation, recursion
   on depth; §4.2). Reynolds's stage relation on one side only (§4.3).
7. **The whole compiler.** FPC (Plotkin; Fiore and Plotkin) with integers, eight passes (simplify after cp0;
   enclose, split closure, hoist; four back-end passes) to a typed
   low-level intermediate language (not "assembly"). Seven passes by an
   equation, split closure by the relation. Adequacy makes the theorem
   equivalent to the operational one. Agda.
8. **The comparison.** Five styles, each proof against its own
   semantics; earlier comparisons cover one pass or phase (Owens et al.,
   Kahn et al.); ours is the first on a whole compiler. Name and cite
   the styles we leave out, and say that comparing them for compiler
   correctness is future work: synthetic domain theory (Hyland 1991,
   Rosolini 1986: not yet in all.bib) and synthetic guarded domain
   theory (Birkedal:2011aa, Mogelberg:2016aa); categorical semantics
   (e.g. Fiore:1994aa); coinductive big-step (Leroy:2009rc),
   pretty-big-step (Chargueraud:2013aa) and functional big-step
   (Owens:2016aa); the partiality monad (Danielsson:2012aa); game
   semantics; action semantics (Mosses:1996rp). Interaction trees
   (Xia:2019aa) get their own clause saying why we did not use them:
   a direct denotation of a higher-order function would need a value
   type that occurs negatively in its own definition (values as
   functions from values to itrees), which Coq's (and Agda's)
   positivity check rejects, so itrees serve first-order languages;
   guarded interaction trees (Frumin, Timany, and Birkedal, POPL 2024;
   not yet in all.bib) model higher-order functions by moving to
   guarded type theory, which is synthetic guarded domain theory again. One sentence, a short list of citations (at most
   three examples per kind).
9. **Findings.** Ranks: interpreters 1,504, graph model 1,808, machines
   2,103, Scott domains 2,485, reduction 3,093; with infrastructure the
   graph model is third (3,352) and Scott domains fifth (10,319).
   simplify: 349 / 411 vs. 508–697. split closure: 450 / 723 vs. 35–126;
   without split closure the graph model would be smallest (1,358 vs.
   1,469). Operational factor: runs track closely for most passes,
   including split closure, and differ more for simplify and hoist.
   Scott domains 1.4 times the graph model, larger in every row but the
   semantics of the languages.
10. **Contributions** (contributions.tex, wording aligned).

Open: approve the RQs; choose the name for x86μ.
