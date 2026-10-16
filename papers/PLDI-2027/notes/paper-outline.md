# Paper outline (draft 2)

Title: TBD. The working title "There is no semantics to rule them all!" fitted a comparison paper and will change.

This is an outline for discussion, not paper text. Numbers come from `loc.py --mu` on master after PR #66 and will change. Paper sections are written double-blind: earlier work in this repository is "we", without saying who (see `history-outline.md`).

**Audience.** The typical PLDI reviewer is not very familiar with denotational semantics. So the paper starts from what they know (the compiler, its passes and languages, §2) before the graph models (§3), explains the models through the compiler's own languages and examples, and introduces each denotational idea just before the proof that needs it.

## Page budget

PLDI 2027 allows **20 pages of text, including the AI-use paragraph, but excluding the Data Availability Statement, references and appendices**, in the ACM `acmsmall` format (single column, 10 pt font, 12 pt leading, text block 5.478 in × 7.884 in), built with `\documentclass[acmsmall,screen,review,anonymous,nonacm]{acmart}` (as `paper.tex` now does). Citations may be author-year (as we use) or numeric. Figures and tables must be legible in grayscale: in Table 1 and Figure 3 mark the winning cells by weight or shape, not by color alone. Budgets include figures and tables. The AI-use paragraph sits in the introduction (its budget includes it); the Data Availability Statement (the artifact) goes after the conclusion and is outside the 20 pages, so details about the artifact can move there from §4.6. The allocation follows the contributions: the compiler proof with the reflection of divergence and the approximant logical relation (§4, especially §4.3) gets the most space, then the comparison (§5), then the background needed to read them (§§2–3); the brief results (§§6–7) and the conclusion get the least.

| Part | Pages | Supports |
|---|---:|---|
| Abstract (with title and front matter) | 0.5 | — |
| 1. Introduction (with contributions) | 3.5 | all |
| 2. The compiler | 1.5 | C2–C4 (what is proved) |
| 3. Background: graph models | 2.0 | C2, C6 (what the reader needs for §4) |
| 4. Proving the compiler correct | 6.5 | C2–C8 (the main claims) |
| 5. Evaluation: comparison with operational approaches | 3.0 | C9 |
| 6. Dynamic typing and errors | 0.5 | RQ4 |
| 7. Discussion: mixing semantics | 0.5 | C9 (a negative result) |
| 8. Related work | 1.5 | positioning beyond the introduction |
| 9. Conclusion and future work | 0.5 | — |
| **Total** | **20.0** | |

Within §4: 4.1 the semantics 1.0, 4.2 equational passes 1.25, 4.3 delay and the approximant logical relation 2.75, 4.4 select and the typed assembly language 0.5, 4.5 adequacy and the end-to-end theorem 0.75, 4.6 mechanization 0.25.

If space runs short, cut in this order: §7 to a few sentences in §5; §6 to a paragraph in §5; §4.6 into §5's setup; §8 down to 1.0 (the introduction already covers the near misses). Protect §4.3 and Table 1 in §5.

## Main claim
A denotational semantics based on graph models can be used to prove a realistic compiler correct, mechanized, all the way to assembly. The compiler goes from ISWIMμ (a call-by-value λ-calculus with recursive types) to a typed x86 in ten passes. Each pass is proved by relating denotations, and adequacy connects the result to running code. The novelty claims and their safe wording are in `related-work.md` (§1): not "the first mechanized denotational compiler proof" (Chlipala 2007 and others), but, to our knowledge, the first multi-pass compiler between different languages proved with graph-model semantics, and the first mechanized adequacy of a denotational semantics for an assembly language.

**The differentiator with Chlipala 2007** (the author's framing; the introduction's "Where this fits" subsection uses it, with the other near misses in "The novelty criteria" above): Chlipala's source is the simply typed λ-calculus, which terminates (it is not Turing complete), so its denotational semantics is straightforward: Coq sets and functions, with type-indexed logical relations. ISWIMμ is Turing complete and admits divergence, so its denotational semantics is more involved: a graph model in which divergence denotes ∅, and passes must reflect it. That is what makes reflection the hard direction and what the approximant logical relation is for (a type index cannot make it well founded, because of μ). The other denotational precedents with a Turing-complete source are first-order (interaction trees: Imp to Asm; Cheng et al. 2026: the CompCert front end) or compile in one pass to a machine with closures, with an operational target (Benton–Hur 2009). Chlipala's own later work switched to operational semantics, and gave Turing completeness as the reason (verified in the primary sources):
  - POPL 2010 ("A Verified Compiler for an Impure Functional Language"), §3, on his earlier denotational work (ICFP 2008, PHOAS): "Our past work gives programs semantics by interpretation into Coq's strongly-normalizing logic CIC; thus, that work cannot be applied directly to Turing-complete programming languages like our source and target languages here." The compiler is then proved against big-step operational semantics, and its theorem still ignores divergence (§1.1: "The theorem we prove in this case study ignores non-termination").
  - PLDI 2007, §12: handling "effectful" features like nontermination and mutability "without first compiling to first-order form … is an interesting open problem"; §2.5: domain theory "is difficult to use … in the setting of constructive type theory".
  - Impurity (references, exceptions) is the new scope of POPL 2010, not the stated reason for the switch.

So the claim to make: a Turing-complete, higher-order source, compiled through closure conversion to assembly, with every intermediate language given a denotational (graph-model) semantics.

## Research questions
- **RQ1. Can a graph-model semantics be used to prove the correctness of a compiler?** Mechanized, through closure conversion, down to assembly, with an end-to-end theorem about running code.
- **RQ2. What does it take?** Which passes are equations, what needs a relation (the approximant logical relation), the supporting properties of the model (consistency, continuity), and adequacy at both ends.
- **RQ3. How does it compare with the operational approaches on the same compiler?** The operational proofs are experimental setup, not contributions: they give an apples-to-apples baseline.
- **RQ4 (brief). How do dynamic typing and errors affect this?**

## The novelty criteria and the near misses

This section is a working tool for the "Where this fits" subsection of the introduction and for §8. It is not a section of the paper. The evidence is in `related-work.md`: verdicts in §1, **quotes from authors on the difficulty in §1.1**, the tier list in §2.0, per-paper tables in §2, details in Parts I–III.

**The four core criteria.** The novelty claim rests on four criteria, which the paper's compiler meets together. They are the fewest that make the claim completely true on the evidence:
- **K1. Denotational.** Every language, source, intermediate and target, has a compositional, extensional model (here a graph model), and the correctness proof of each pass relates the denotations of that pass's source and target. A definitional interpreter, a term model or an equational λ-theory does not count, and neither does a proof that uses an operational semantics for either side of a pass, even if the other side has a denotation.
- **K2a. General recursion.** The source has general recursion, so it is Turing complete and programs can diverge.
- **K2b. Total correctness proof.** The correctness theorem preserves *and reflects* divergence: a program diverges iff its translation does. A theorem for terminating programs only, or in one direction only, does not meet it. K2b applies only when K2a holds (a total source has no divergence to reflect, and already misses K2a, so the miss is counted once).
- **K3. Closure conversion.** A pass lowers closures to first-order data. Defunctionalization counts. A target with primitive closures does not, and a first-order source has no closures to convert.

**Two tie-breakers, not criteria.** **K4**: multi-pass, ending in an assembly-level language. **K5**: mechanized. Earlier searches showed neither is needed for novelty: no prior work meets K1, K2a, K2b and K3 together, whether or not it meets K4 or K5. They only rank works within a tier or group. (The paper still claims both, separately: C4, C7 and C9 in `related-work.md`.)

**Why K2b is the center of the story.** In a graph model divergence is ∅, so preserving divergence is ⟦src⟧ ⊆ ⟦tgt⟧ and reflecting it is ⟦tgt⟧ ⊆ ⟦src⟧. The delay pass's reflection proof (the approximant logical relation) is what K2b costs in a denotational proof of closure conversion for a source with recursion. The near misses on K2b are therefore the heart of the introduction's comparison, and the authors' own words on the difficulty (`related-work.md` §1.1) are worth quoting:
- Nielsen 2000, the closest denotational proof, proves "weak correctness" only and says "Eventually, we want to prove full correctness, i.e., semantic equivalence of the two programs." His relation is one-sided (⊥ related to everything) and uses fixed-point induction, which is not available for the reverse direction.
- Banerjee–Heintze–Riecke 2001: "we know of no other proofs of correctness (that is, both directions) for ordinary or CFA-based defunctionalization in the presence of recursion", and the earlier proofs "prove only one direction of correctness"; their own reverse direction needs "a lexicographic induction … due to recursion", and their source is operational.
- Chlipala 2010 turned to operational semantics because the earlier denotational work "cannot be applied directly to Turing-complete programming languages", and his theorem "ignores non-termination".
- Stoy 1981 on why the relation is hard: it relates "an infinitary abstract object … with its finitary representation", the existence of the predicates "is still an open question", and "it is the basis of the induction which fails" (check the OCR against the printed page).
- Benton–Hur 2009 needed relations that "were of necessity asymmetric" (Hur–Dreyer's words), with a step index on the machine side and an admissible closure on the denotation side.

**Tiers.** A work's tier is the number of K1, K2a, K2b, K3 it misses (✗ and ~ both count). The introduction treats Tier 1 first and goes down; §8 does the same for what the introduction leaves out. Within a tier, order the works by the criterion missed, K2b first (closest to the delay proof), then K2a, K3, K1, and then by K4 and K5 (closer first). The column "Divergence" in the table says how each work treats divergence, since that is what the introduction compares.

**The near misses, for the introduction.** ✓ meets it, ✗ misses it, ~ partly.

| Tier | Misses | Work | K4 | K5 | Divergence | What to say in the introduction |
|---|---|---|---|---|---|---|
| 1 | K2b | Nielsen 2000 | ✗ | ✗ | Forward only: a terminating source gives the same value in the target; a diverging source says nothing about the target. | **The closest denotational work, and the one to compare in detail.** CPO denotations for source and target, a simply typed higher-order language with recursive functions, defunctionalization, logical relations, on paper. His "weak correctness" is the preservation direction; he leaves reflection as future work. Quote his "Eventually, we want to prove full correctness". |
| 1 | K2a | Chlipala 2007 | ✓ | ✓ | None: the source is total. | Denotational throughout, closure conversion, down to assembly, in Coq. But the source is the simply typed λ-calculus without recursion, so there is no divergence to reflect, and the semantics is Coq functions with type-indexed relations. His later compiler turned to operational semantics because the denotational method "cannot be applied directly to Turing-complete programming languages". |
| 1 | K3 | Clinger 1984; VLISP | ✗; ~ | ✗ | Equal meanings in one domain (Clinger), so ⊥ is covered with no relation between two models; VLISP's machine faithfulness is one direction. | The right language (Scheme) and a denotational proof that covers divergence, but on paper, and the target has closure values, so there is no closure conversion and no relation between two models. |
| 1 | K3 | Siek 2017 (the inliner) | ✗ | ✓ | Equal graph-model denotations (∅ for divergence). | The only prior mechanized use of a graph model for a transformation, for an untyped λ-calculus with general recursion, but a same-language optimization: it does no closure conversion. Cite in the third person. |
| 1 | K3 | Interaction trees (Imp to Asm); Cheng et al. 2026; Polak 1980/81 | ~; ~; ~ | ✓; ✓; part. | Termination-sensitive bisimulation; sets of behaviours including divergence; equal denotations. | Denotational compiler proofs that do cover divergence, mechanized (Polak partly), but first-order: there are no closures to convert. |
| 1 | K1 | Pottier & Gauthier 2004/2006 | ✗ | ✗ | Preserves convergence and divergence ("p ⇑ implies ⟦p⟧ ⇑"), by a simulation between operational configurations. | Defunctionalization of an untyped call-by-value language with recursion, proved correct by simulation in the usual operational way, with divergence preserved. The operational counterpart of what we do for closure conversion; their remark that an untyped statement is stronger than the typed logical-relation proofs of Nielsen and Bell–Bellegarde–Hook is quotable. |
| 1 | K1 | CakeML backend; CertiCoq | ✓; ~ | ✓ | Clocked big-step semantics; step-indexed relations. | The same shape of compiler (higher-order source with recursion, closure conversion, many passes) proved operationally and preserving divergence. The state of the art we compare against, and the baseline for our three operational proofs. |
| 1 | K1 | Banerjee–Heintze–Riecke 2001 | ✗ | ✗ | Source evaluates to `n` iff the target does; by the target's adequacy and a lexicographic induction on unwindings. | Defunctionalization of a typed higher-order language with recursion, proved correct in both directions. But the source is operational and only the first-order target has a denotation, so the proof is not a relation between two denotations. One pass, on paper, main proof a sketch. They say they "know of no other proofs of correctness (that is, both directions) … in the presence of recursion". Danvy and Nielsen's 2001 summary gives the same split in one sentence: "Nielsen proved its partial correctness using denotational semantics; and Banerjee, Heintze and Riecke proved its total correctness using operational semantics." |
| 2 | K1, K3 | CompCert | ✓ | ✓ | Preservation of terminating, diverging and wrong behaviours, by simulations (how reflection is obtained: check Leroy's papers). | The most famous compiler-correctness proof, and operational. Multi-pass to assembly, Turing-complete C, divergence covered. But the source is first-order, so there are no closures to convert, and the proof is by simulations rather than a relation between denotations. The standard against which the field measures verified compilers, and the reason the abstract says verified compilers are almost entirely operational. |
| 2 | K1, K3 | Benton–Hur 2009 | ✗ | ✓ | Both directions, with a step-indexed relation on the machine side and an admissible closure on the denotation side. | Mechanized, recursion, both directions of a denotational-to-machine correctness. But one pass, to an SECD machine that has closures, with an operational target. |
| 2 | K1, K3 | Bahr–Hutton calculated compilers (2022; newest: Bahr, "Safety First", ICFP 2026); Danielsson 2012 | ✗ | ✓ | Partiality monad; bisimilarity. | Mechanized, untyped higher-order source, divergence handled. But the semantics is a definitional interpreter with environments and closures (Danielsson says it is not denotational; the word does not occur in Bahr's 2026 paper, which uses choice trees and proves bisimilarity only for safe, well-typed programs), the VM keeps closures, and each is one pass. |
| 2 | K1, K2b | Chlipala 2010; Steckler–Wand 1994/1997 | ✓; ✗ | ✓; ✗ | Both ignore divergence ("ignores non-termination"; partial correctness). | Closure conversion for untyped languages, but operational and forward only. |
| 2 | K1, K2a~ | Wand 1991 | ✗ | ✗ | Not applicable (tiny language). | Handles closure and procedure representations, but inside an equational λ-theory, which is not an extensional model, on paper. |
| 3 | K1, K2b, K3 | Pardo et al. 2018 | ✓ | ✓ | One direction only: a defined result implies the assembler run reaches it; no divergence claim. | Agda; clocked denotations for a While language and a stack language, down to an idealized assembler; first-order, and the assembler is operational. Also the nearest adequacy-style statement for an assembler. |

**Adequacy near misses.** One sentence each, after the table, closest first:
- Tune & Kavvos 2026 (Agda): adequacy of a set-theoretic semantics against CK/CEK machines, but for a total call-by-push-value language and for first-order observations, with no compiler.
- Pardo et al. 2018: one-direction adequacy of a stack language's denotation against the compiled assembler's run; the assembler has no denotational semantics of its own.
- Chlipala 2007 and interaction trees: denotations of an assembly language, but no machine to be adequate against.
- VLISP: the same idea on paper, for a byte-code machine, one direction.

**Left to §8, by tier.**
- **Tier 1:** the typed and operational closure-conversion literature whose source has recursion (Ahmed–Blume, Pilsner, Pyrosome, Wang–Nadathur, Perconti–Ahmed), which misses only K1 like CakeML and CertiCoq; the other first-order denotational compilers (Vellvm, HELIX, Vélus, the LCF work of Milner–Weyhrauch and Cohn).
- **Tier 2:** Huang and Yallop 2023 (defunctionalization for a total, dependently typed language: operational, forward direction, no divergence); lambda lifting (Fischbach–Hannan, Kerneis–Chroboczek; Levy and Reeves 2026 formalise a lifting specification in Lean but prove no semantic preservation of their own); Sullivan–Wand 1996 and Wand–Sullivan 1997 (an "almost-denotational" term model, so K1; lambda lifting, not closure conversion; tentative); Rodríguez–Pagano–Fridlender 2016; Martin & Toal 1991; Morris and Thatcher–Wagner–Wright; Cogent and McKinna–Wright; the typed, total closure-conversion papers (Minamide–Morrisett–Harper, Bowman–Ahmed, Beluga).
- **Tier 3:** Pickard–Hutton 2021 and Pickard's 2026 thesis (calculation for typed total languages); Bahr–Hutton 2015 and 2020 (converging behaviour only); Œuf (only the source has a denotation, the source is total, closures are explicit); Siek 2025 (OlivierFest; four verified passes to an x86-flavored language, operational, first-order and total; third person).
- **Not compiler proofs, so no tier:** graph-model and filter-model background, mechanized domain theory, the relations literature (where the authors' remarks on the difficulty of the relations also go, `related-work.md` §1.1), the adequacy theory (Winskel, Martin-Löf, Abramsky), and game semantics.

**Rule for choosing.** A work belongs in the introduction if a reviewer who knows it could reasonably say "this already does what you claim", or if it shows how others treated divergence in a closure-conversion-like proof. It belongs in §8 if it is background or a contrast the reviewer would not raise against the claim. Revisit the table when the claims are reworded.

## 1. Introduction (3.5 pages)
- **Motivation.** Denotational semantics promises compositional, equational reasoning about programs, yet mechanized compiler verification has been operational, with CompCert's simulations as the standard. Graph models are an elementary, set-theoretic form of denotational semantics (Plotkin, Scott, Engeler) that is easy to mechanize, but they have been used for little beyond adequacy and source-level optimizations.
- **What we did (RQ1).** We proved a ten-pass compiler correct with graph-model semantics for every intermediate language, ending in an end-to-end theorem: the source and the compiled x86 program stop with the same constant, or both diverge.
- **Where this fits: closely related work** (a subsection of the introduction, about a page and a half; see "The novelty criteria" above). It is organised around one question: **how has prior work treated divergence in a proof of closure conversion?** It does four things:
  - states the four core criteria the compiler meets together (K1 denotational, K2a general recursion, K2b a total correctness proof that preserves and reflects divergence, K3 closure conversion) and says each prior work meets some but not all of them;
  - walks through the **near misses** in order of tier, Tier 1 first (one criterion missed) and then Tier 2 and Tier 3, naming for each the criterion it misses and how it treats divergence; the K2b near misses (Nielsen, then Chlipala 2010, Steckler–Wand) get the most space, and the authors' own words on the difficulty are quoted (`related-work.md` §1.1): Nielsen's "weak correctness" and "Eventually, we want to prove full correctness", Banerjee–Heintze–Riecke's "we know of no other proofs of correctness (that is, both directions) … in the presence of recursion", Chlipala's "cannot be applied directly to Turing-complete programming languages";
  - explains **Banerjee–Heintze–Riecke** carefully, because the situation is subtle: they prove defunctionalization correct in both directions for a higher-order language with recursion, so on divergence they match us, but their source has only an operational semantics and only the first-order target is given a denotation, so their proof relates source evaluation to target denotation rather than two denotations (it is not a "denotational compiler proof" in the abstract's sense); say what each of those facts buys and costs, and why we do not claim priority over them on K2b;
  - connects the diagnosis to the technical core: preservation is the easy direction (Nielsen's one-sided relation with fixed-point induction suffices), and the delay pass's reflection direction is what needs the approximant logical relation (§4.3);
  - ends by saying that the next section's compiler is the first that meets all four, with "to our knowledge", and points to §8 for the rest of the literature (the tie-breakers K4 and K5 are mentioned in passing, not as part of the claim).
  Everything not named there is left to §8.
- **Mechanization, artifact, and AI disclosure.** One sentence: everything is mechanized in Agda (`--safe`, standard library only), and the proofs are available in the artifact. Immediately after it, the disclosure of AI assistance (ACM policy). It goes here, not in threats to validity, because it is not a threat to validity.
- **What it took (RQ2).**
  - Most passes are equations of denotations, proved one construct at a time.
  - Closure lowering (delay) needs a new kind of relation for its reflection direction: the approximant logical relation.
- **How it compares (RQ3).** We proved the same compiler in three operational styles under the same accounting rules:
  - totals: graph 1958, CEK 2258, interpreter 1653, reduction 3207;
  - the graph model is smallest for equational passes (simplify 360 against 584–715);
  - it is costliest for delay (524 against 35–139).
  - **Prior comparisons are smaller in scope** (`related-work.md` §1.3), and the introduction should say so in a sentence or two, to be accurate about novelty: Kahn, Hoffmann and Li (2025) compare three operational semantics (small-step, big-step and their big-stop) by the lines of Agda needed to prove one compilation to a K machine correct; Owens et al. (2016) compare relational and functional big-step semantics on one compiler phase (43 against 18 lines); Leroy and Grall (2009) and Leroy's lecture notes relate the styles by equivalence theorems but prove each compiler under one style; Knothe and Bringmann (2026) combine small-step and big-step semantics in one CompCert pipeline without comparing costs. Ours is, to our knowledge, the first on a whole multi-pass compiler to assembly, and the first to include a denotational style. Cite them again in §5 and §8.
- **Contributions** (`contributions.tex`, PR #82): one sentence each, with a forward reference: the graph-model compiler proof; approximant logical relations; adequacy for the source and the assembly language, and the end-to-end theorem; the comparison, on one ten-pass compiler, of a denotational style with three operational styles (stated narrowly, since earlier comparisons of semantic styles exist for one pass or phase).

## 2. The compiler (1.5 pages)
- **ISWIMμ:** integers, tuples, sums, primitives, and iso-recursive types with `fold`/`unfold`. There is no `fix`: recursion and divergence come from the Z combinator, typed through μ.
- **The pipeline:**
  - simplify (a simplified cp0);
  - closure conversion in four passes: enclose, optimize, concretize, delay;
  - globalize, remove complex operands, lift locals, explicate control, select instructions;
  - the target X86μ, a typed assembly language.
- **Intrinsically typed intermediate languages:** no pass needs a scoping or typing precondition.
- Fig. 1: the pipeline.

## 3. Background: graph models (2.0 pages)
- **Why a graph model rather than Scott domains** (the introduction only summarizes this and points here, as `sec:graph-models`). The graph model is elementary: a denotation is just a set, with no complete partial orders, continuous functions or inverse limits. The evidence, all counted like `loc.py` (no comments, blank lines or imports):
  - the core of our graph model (values, consistency, generic machinery for operators) is 364 lines of Agda, about 1,200 with the meanings of the operators of all our languages (`loc.md`, infrastructure table: 364 + 623 + 235);
  - the Scott-domain pilot (branch `scott-pilot`; source language, Clos2 and enclose of the earlier untyped compiler) builds on Tom de Jong's domain theory in TypeTopology: its own constructions (sums, lifting, products and exponentials of dcpos, locally continuous functors, the bilimit solution of the domain equation) are 847 lines, on top of about 5,400 lines of TypeTopology's domain theory (13 `DomainTheory` modules reached by its imports; about 25,900 lines counting all 120 TypeTopology modules reached, including the univalent foundations); its operators and semantics of signatures are 185 more, the semantics of ISWIM, Clos2 and primitives 75, the proof of enclose 118;
  - the pilot assumes propositional truncation, function extensionality and propositional extensionality; the graph model needs none of them (and the whole development is `--safe`, standard library only);
  - Benton, Birkedal, Kennedy and Varming report "around 4400 lines" of Coq for their category and domain-theory library, including recursive domain equations (`related-denot/benton-birkedal-kennedy-varming-formalizing-domains.pdf`).
  Cite TypeTopology (`refs.bib: TypeTopology`) and BBKV10.
- **Through the compiler's own languages.** Examples come from ISWIMμ and the intermediate languages of §2 (e.g. the meaning of a λ, of an application, of a diverging Z-combinator loop), not from the pure λ-calculus.
- **Denotations.** A denotation is a set of finite values. A function's finite value is a finite table of input/output entries, and application ⟦L M⟧ρ collects the outputs of the tables in ⟦L⟧ρ whose inputs are covered by ⟦M⟧ρ.
- **The properties the proofs rely on:**
  - monotonicity and continuity;
  - consistency, with binders that bind only consistent finite sets;
  - divergence denotes ∅.
- **Why reflection is the hard direction.** Divergence is the absence of elements, so a forward relation cannot carry it. A correctness statement ⟦src⟧ ≃ ⟦tgt⟧ therefore needs both inclusions.

## 4. Proving the compiler correct with graph models (RQ1, RQ2) (6.5 pages)
- **4.1 The semantics** (1.0 page) of each intermediate language as a graph model. Closures, code tables, frames and control-flow graphs all get graph-model meanings.
- **4.2 Equational passes** (1.25 pages). For simplify, enclose, optimize, concretize, globalize, rco, lift locals and explicate, ⟦pass M⟧ ≃ ⟦M⟧ is proved construct by construct from operator laws. Typical shapes and sizes.
- **4.3 Delay and the approximant logical relation** (2.75 pages; the technical core):
  - **the problem:** a target call takes its code from `car` and its environment from `cdr` separately;
  - **why the natural relations fail** (`history-outline.md`): single values; whole sets (▷ with nothing to discharge it); element depth (as in Pitts's projections); one target point in an infinite context;
  - **the insight:** only one side needs to shrink, and the car/cdr matching happens inside the index;
  - **the definition:** 𝖠𝖫𝖱(D, V′), its layers, fuel as a termination device, depth irrelevance;
  - **why a type index cannot replace the depth index:** at μX. X ⇒ Int the application case returns to the same type.
  - **comparison with Nielsen 2000 and with Pitts (to do, needed for §4.3 and §8):** Nielsen's relation (`related-work.md` Part II §1) is the closest denotation-to-denotation proof of a closure-conversion-like pass. It is type-indexed, relates source denotations to defunctionalized target denotations, treats ⊥ as related to everything, and uses fixed-point induction. It proves only the forward direction ("weak correctness"), so it has no analogue of our reflection proof. Say how ours differs (finite-approximation index on the target, reflection, recursive types) and why his method does not extend, and compare with Pitts's relations for recursive types (Part III B1, B2).
- **4.4 Select and the typed assembly language** (0.5 page). The meaning of X86μ, and select proved as an equation.
- **4.5 Adequacy and the end-to-end theorem** (0.75 page):
  - adequacy for ISWIMμ and for X86μ against their interpreters (PR #76; the CEK-based proofs are an uncounted alternative);
  - no-error lemmas;
  - the end theorem, the same one the operational proofs state.
- **4.6 Mechanization** (0.25 page). Agda (`--safe`, stdlib only), the audit surface, sizes.

## 5. Evaluation: comparison with operational approaches (RQ3) (3.0 pages)
- **Setup.** The same compiler proved with CEK machines and simulations, clocked interpreters with value relations, and reduction semantics with simulations, each a best effort. These are the baseline, not contributions.
- **Prior comparisons of semantic styles** (`related-work.md` §1.3), to be cited here and in §8, and the reason the claim is narrow: Kahn, Hoffmann and Li 2025 (three operational styles, one compilation to a K machine, Agda, a table of proof sizes: small-step completeness is the costly part), Owens et al. 2016 (relational against functional big-step on one phase, 43 against 18 lines), and Leroy and Grall's folklore that big-step suits compiler proofs. Ours differs in scale (a ten-pass compiler to assembly) and in including a denotational style.
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
  - adequacy (1532 lines), reported as its own result: with the graph semantics taken as definitional, the denotational proof is complete without it, and adequacy connects it to running code;
  - the audit surface.
- **Threats to validity:**
  - lines of Agda as a proxy for effort;
  - effort and expertise per style;
  - what infrastructure each style could share.

## 6. Dynamic typing and errors (RQ4, brief) (0.5 page)
- **The same compiler from dynamically typed ISWIM:** cast insertion, `Any = μX. Σ_G G[X]`, `project`/`chk`, and a graph model with errors to observe them.
- **Totals barely move:** graph 2064 → 1958, CEK 2390 → 2258, interpreter 1719 → 1653, reduction 3320 → 3207.
- **Delay's cost comes from recursive types, not errors:** graph delay goes 552 → 524 (errors account for about 28 lines).

## 7. Discussion: mixing semantics (a negative result, one paragraph) (0.5 page)
- The idea: use, for each pass, the cheapest style, joined by bridges (adequacy of a language's graph semantics against its interpreter) where the style changes.
- Measured (PR #72, `notes/mixed-semantics.md`): graph model for simplify, interpreter for the rest, one bridge at ISWIMμ: 1839 lines, against 1653 for the pure interpreter proof. A bridge (395 lines) costs about as much as a whole pass proof and more than the largest saving (simplify, 273); more splits are estimated at 2530–3265.
- Worth a paragraph and a small table: per-pass minima do not add up. By-products: adequacy against the interpreter is cheaper than against the CEK machine (395 against 464), and it gives the graph model a cheaper route to running code.

## 8. Related work (1.5 pages)
The "not so closely related" work, ordered by tier (number of K1, K2a, K2b, K3 missed), starting with the lowest tier. The works in the introduction's table (Nielsen, Chlipala 2007 and 2010, CompCert, Clinger and VLISP, Siek 2017, interaction trees, Cheng et al., Polak, CakeML, CertiCoq, Banerjee–Heintze–Riecke, Benton–Hur, the calculated compilers and Danielsson, Steckler–Wand, Wand 1991, Pardo et al.) get at most a back-reference here. Organised as in `related-work.md` (§2.0 there is the tier list).
- **Tier 1: operational and type-theoretic closure conversion, and further first-order denotational compilers.** Ahmed–Blume, Pilsner, Hur–Dreyer, Pyrosome, Wang–Nadathur, Perconti–Ahmed (each misses only K1 when its source has recursion, and shows what the operational methods already achieve); Vellvm, HELIX, Vélus, and the LCF work (each misses only K3).
- **Tier 2: other near misses.** CompCertO and CompCertTSO (the CompCert variants, with game-inspired interfaces and weak memory); Sullivan–Wand and Wand–Sullivan (the operationally-based term model: the nearest thing to "almost denotational", and the reason K1 says extensional model); Rodríguez–Pagano–Fridlender; Martin & Toal; the historical commuting-square line (Morris, Thatcher–Wagner–Wright); Cogent and McKinna–Wright; typed, total closure conversion (Minamide–Morrisett–Harper, Bowman–Ahmed, Beluga, Sullivan–Downen–Ariola, whose delayed environments are close in spirit to the delay pass).
- **Tier 3:** Bahr–Hutton 2015 and 2020 (converging behaviour only), Œuf (a denotation for the source only; every pass proved operationally), Siek 2025 (OlivierFest; cited in the third person).
- **Not compiler proofs, so outside the tiers:**
  - graph and filter models and their mechanizations: Plotkin, Scott, Engeler, Barendregt–Coppo–Dezani, Siek 2017 and PLFA (third person), and the mechanized domain theory of Benton–Kennedy–Varming, de Jong–Escardó and Mosses;
  - **Pitts's relational properties of domains, as an alternative route** (the introduction gives two sentences and points here, as `sec:related`). Draft text moved from the introduction:
    > A different route to the same theorem would replace the graph model by traditional domain theory and appeal to Pitts [1996]. Pitts works with recursively defined domains in the category of pointed cpos (countable chains have least upper bounds) and strict continuous functions, solved as minimal invariants of locally continuous functors; his method is deliberately not restricted to Scott domains (he notes that Martin-Löf's information-system method "applies only to Scott domains (precluding the use of constructors like the Plotkin powerdomain)", §5). He proves that a relation specified by the same recursive equation as the domain, with both positive and negative occurrences of the relation (so not a monotone operator, and Knaster–Tarski does not apply), exists and is unique, because the domain is the minimal invariant of its defining functor (Theorem 4.16, with Freyd's mixed initiality/finality). He applies the result to computational adequacy (§5, a fragment of Standard ML with datatype declarations) and to induction and co-induction on a single domain (§6), and he notes (p. 68) that the same theory underlies relations between two denotational semantics, such as the relation of Reynolds [1974] between direct and continuation semantics, without working that case out. Whether Pitts's framework applies to a graph model is unclear: the graph model's values solve a set equation (finite values built from base values and finite tables, an inductive type), and its denotations are arbitrary sets of such values ordered by inclusion, not a recursively defined cppo given as the minimal invariant of a locally continuous functor. (An earlier draft said "a graph model has no domain equation"; that is not technically accurate, so avoid it.) Whether his method would make the reflection proof for delay easier, at the price of the domain theory (see the Scott-domain pilot in §3), remains an open question.
    Also compare with Nielsen's type-indexed relation here (open item 0).
  - relations for adequacy versus relations between two denotations: Reynolds 1974 (the tower), Pitts, Milne–Strachey, Stoy, Mulmuley, Meyer–Wand, Filinski, the step-indexed and guarded alternatives, and Martin-Löf, Winskel and Abramsky for finite-element indexing in adequacy proofs; this paragraph carries the claim for the approximant logical relation, and is the place for the authors' remarks on why such relations are hard (`related-work.md` §1.1: non-monotone fixed points, reflexive domains, existence "an open question");
  - comparisons of semantic styles for compiler proofs: Kahn–Hoffmann–Li 2025, Owens et al. 2016, Leroy–Grall 2009, Leroy 2010, Knothe–Bringmann 2026 (small-step and big-step in one CompCert pipeline, the mixed-semantics idea of §7), Martin and Toal 1991;
  - adequacy for machines and assembly beyond the two named in the introduction (the decoder DSL, guarded interaction trees);
  - game semantics (Ghica; CompCertO's interfaces) as a contrast.

## 9. Conclusion and future work (0.5 page)
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
- Novelty claims, to be worded after the literature check. Open items: (0) compare our approximant logical relation with Nielsen's relation and Pitts's (see §4.3); (1) the abstract's two horns do not cover Nielsen 2000 and Banerjee–Heintze–Riecke 2001 (see "The novelty criteria"); the abstract now has a third horn for K2b ("prove only that terminating programs are preserved"); Banerjee et al. are not covered by it, but they are not a denotational proof under K1, so the abstract's "denotational compiler proofs" excludes them. (2) Sullivan–Wand and Wand–Sullivan were read only to the abstracts and introductions; check that their lambda lifting is not a closure-conversion proof and that their term model is not extensional. (3) Nielsen's and Banerjee et al.'s proofs are on paper (one a sketch), so the safest framing of the claim stresses what they lack, divergence covered (K2) and an extensional model on both sides (K1); that ours is also mechanized and goes to assembly is a further, separate distinction.
- Whether the introduction should list the criteria K1, K2a, K2b, K3 explicitly or just walk through the near misses.
- The page budget for §4.3 against §5: settled in "Page budget" (2.75 against 3.0); revisit after drafting §4.3.
- Matthew Heimerdinger's affiliation.
- The artifact: an anonymized copy of the Agda development.
