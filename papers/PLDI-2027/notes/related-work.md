# Related work: literature notes for the compiler-correctness paper

Research notes, not paper text. This file combines three earlier notes files: `novelty-literature.md` (now **Part I**), `related-work-closure-conversion.md` (now **Part II**) and `related-work-literature.md` (now **Part III**). The sections below come first: the novelty claims and their verdicts (§1), a table that sorts every paper in Parts I–III by what it implies for those claims (§2), and an index of the local PDFs (§3).

**Layout**

- [§1 Novelty claims and verdicts](#1-novelty-claims-and-verdicts): what the abstract, the outline and `contributions.tex` assert, with safe wording.
- [§2 The literature, categorized against the claims](#2-the-literature-categorized-against-the-claims): one table per kind of work.
- [§3 Local PDFs](#3-local-pdfs): the contents of `related-denot/`.
- **Part I**, compiler correctness with denotational semantics, graph-model mechanizations, adequacy for assembly (the 2026-10-15 novelty search).
- **Part II**, closure conversion, denotational semantics and mechanized proofs (the 2026-10-09 survey for the delay pass).
- **Part III**, logical relations over finite elements, recursive domains, and denotation-to-denotation relations (the 2026-10-14 notes, with the name check for "approximant").

**Evidence tags.** Each part keeps the tags it was written with; they mean roughly the same thing.

| Strength | Part I | Part II | Part III |
|---|---|---|---|
| Read in the primary source | **[V]** (also **[V-notes]**: verified in earlier notes, not re-read) | **[read]** | **[V]** |
| Abstract, metadata or snippets only | **[A]** | **[abstract]** | **[U]** (secondary) |
| Memory or cited without checking; do not cite before checking | **[M]** | **[known]** | **[U]** |

The PDFs read in the third pass are in `related-denot/` at the repository root (see Part I §3). That directory is not in git, so the PDFs are not on GitHub. Older text in Parts I and III still says `related-denot/` or `related-denot/`; both mean `related-denot/`.

---

## 1. Novelty claims and verdicts

The claims come from three places:

- **A1 and A2** (and the A3 horn we found we need to add) are the horns of the literature claim in `abstract.tex`: the denotational compiler proofs in the literature, on paper or mechanized, either (A1) are limited to source languages that are first-order or strongly normalizing, or (A2) compile to target languages that treat closures as primitive values and so avoid closure conversion. The abstract also opens with "verified compilers today are almost entirely operational".
- **C1–C10** are the candidate claims from the novelty search. `paper-outline.md` (main claim, RQ1–RQ3) and `contributions.tex` use C2–C4, C6, C7 and C9; C1 is a claim to avoid; C5 and C8 are distinguishing features rather than priority claims; C10 is an engineering claim.
- The abstract's own contributions map as follows: "a graph-model proof of a ten-pass compiler, mechanized in Agda" is C2, C3 and C4; "most passes are proved by an equation between denotations" is C5; "approximant logical relations" is C6; adequacy and the end-to-end theorem are C7 and C8; "the same compiler in three operational styles" is C9.

| # | Claim | Where it appears | Verdict | Safe phrasing |
|---|---|---|---|---|
| A1/A2 | Every denotational compiler proof in the literature has a source that is first-order or strongly normalizing (A1), or a target with primitive closures (A2) | Abstract | **Not supported as stated.** Nielsen 2000 gives a denotational proof (CPO semantics, source and target) of defunctionalization for a simply typed higher-order language with recursive functions, but only the forward direction (terminating programs); Banerjee–Heintze–Riecke 2001 prove defunctionalization correct in both directions, but the source has only an operational semantics. Neither is first-order, strongly normalizing, or a target with primitive closures. The claim is true with a third horn: (A3) the proof preserves but does not reflect divergence (K2b), or gives a denotation to only one side of the pass (K1). Otherwise each denotational compiler proof found falls on A1 or A2 (see §2). Wand 1991 and Sullivan–Wand are not extensional-model proofs. | "The denotational compiler proofs we know of either have first-order or strongly normalizing sources, or compile to targets with primitive closures, or establish only that terminating programs are preserved, or give a denotation to only one side of the pass." Keep "we know of". |
| C1 | "First mechanized compiler-correctness proof using denotational semantics" | Not in the paper; a claim to avoid | **Contradicted** by Chlipala07 (Coq, every intermediate language), Benton–Hur 2009 (source), XiaITrees20 (Imp/Asm), Cheng et al. 2026 (CompCert front end), and long before them by Polak 1980/81 (denotational source and target, compiler program machine-checked with the Stanford verifier, semantic theory by hand) and, per Polak, Milner–Weyhrauch 1972 and Cohn 1979 in LCF; also Martin–Toal 1991 (HOL), Pardo et al. 2018 (Agda; clocked denotational semantics for While and a stack IL, down to an idealized assembler) and Bourke et al. 2025 (Vélus). All of the pre-2007 ones are first-order. Polak's book (now read) confirms the thesis-based description. | Do not claim. Cite Chlipala, Benton–Hur, ITrees and Cheng et al. as the modern denotational line, and Polak (with the LCF work) as the historical mechanized one. |
| C2 | "First verified compiler whose correctness is proved with graph-model semantics" | Outline (main claim); contributions; abstract | **Supported, to our knowledge.** The only prior mechanized graph-model transformation proof is Siek's 2017 inliner (same language). PLFA has none. | "To our knowledge, this is the first verified multi-pass compiler, beyond same-language optimizations [Siek 2017], whose correctness is stated and proved using graph-model (Plotkin/Engeler-style) denotational semantics for every intermediate language." |
| C3 | "First denotational proof of closure conversion" | Abstract (implicitly, through A1/A2); contributions | **Contradicted as stated** (Chlipala07 CPS→CC). Wand91 handles procedure representations on paper in an equational λ-theory, which is not a denotational semantics (see the entry above), so it is related work but not a counterexample. **Qualified version supported:** first for a source with general recursion and divergence (and recursive types, plus an untyped variant), denotation to denotation, mechanized. | "Unlike Chlipala's typed, total source, ours has general recursion through iso-recursive types; to our knowledge this is the first mechanized denotation-to-denotation proof of closure conversion for such a language." |
| C4 | "First mechanized denotational correctness proof of a compiler from a higher-order language with general recursion to assembly" | Outline (main claim); contributions | **Qualified.** Benton–Hur 2009 is mechanized, with recursion, but compiles to an SECD machine with closures (one pass, no closure conversion, operational target). VLISP is untyped Scheme to byte code but on paper. Chlipala07 is total. | "…the first mechanized compiler from a higher-order language with general recursion to an assembly language in which every pass, including closure conversion, is proved using denotational semantics." Keep "to our knowledge". |
| C5 | "Per-pass correctness is equality of denotations, ⟦src⟧ ≃ ⟦tgt⟧" | Abstract; outline §4.2 | **Qualified, as a distinguishing feature, not a priority claim.** Chlipala uses type-indexed logical relations; Benton–Hur uses realizability. The Wand–Clinger single-model approach also equates meanings in one model (on paper). | "For most passes, correctness is literally equality of graph-model denotations; only closure lowering needs a relation." |
| C6 | "New approximant logical relation between two graph-model denotations" | Abstract; contributions; outline §4.3 | **Supported, to our knowledge** (per Part III: no denotation-to-denotation relation indexed by finite elements was found). Polak 1980 (§IV.5.3.4–5) adds one more heterogeneous source/target predicate family, recursive and non-monotone, whose existence is assumed by appeal to Reynolds 1974; not indexed by finite elements. Now read: **Filinski 2007** builds its relations between two monadic interpretations at recursive types the Pitts way (Theorem 39, "Existence of Invariant Relations", p. 65: Knaster–Tarski on admissible relations for existence, minimal invariance for uniqueness), type-indexed over the metalanguage's types, symmetric, for two semantics of the *same* object language; no finite elements. **Stoy 1981** builds its predicates on the inverse-limit "approximation domains" and takes "the conjunction of the results" (p. 156); its order-asymmetric ("weaker than") predicates relate a denotation to an *interpreter*, not two denotations. **Meyer–Wand 1985** use λ-definable retractions and a type-indexed "concrete invariant", typed and without fixed points. **Nielsen 2000** relates the CPO denotations of a source and its defunctionalized target by a type-indexed, one-sided (⊥ related to everything) logical relation, with fixed-point induction; it proves only the preservation direction and has no recursive types. It does not change the verdict, but ours must be compared with it (and with Pitts's relations) in the paper. None changes the verdict. Remaining gaps: Milne–Strachey 1976 and Mulmuley's 1987 book. | "To our knowledge, the first relation between two denotational semantics defined by recursion on a finite approximation of one of the two denotations." (Not "indexed by": the relation has just the two denotations as parameters, with no step or type index.) |
| C7 | "First mechanized adequacy of a graph model (or of any denotational semantics) for an assembly language against an abstract machine" | Outline (main claim); contributions; abstract (adequacy) | **Supported, to our knowledge.** Chlipala and ITrees give assembly denotations without machine adequacy. VLISP's byte-code faithfulness (M92B093, now read) is on paper and one direction only. Polak's and Clinger's target machines have only a denotation (no machine, no adequacy). **The parenthetical "(or of any denotational semantics) … against an abstract machine" must not be stated without "assembly":** Tune & Kavvos 2026 [V] mechanize in Agda the adequacy of a set-theoretic semantics against CK and CEK machines (total CBPV, first-order observations, one direction). Pardo et al. 2018 [V] mechanize in Agda a one-direction "computational adequacy" of the clocked denotation of a stack IL against the small-step run of the compiled assembler code; Assm itself gets no denotation. | "To our knowledge, the first mechanized adequacy proof for a denotational (graph-model) semantics of an assembly-level language with respect to a machine for that language." Cite Tune & Kavvos (CK/CEK, total) and Pardo et al. (stack IL to assembler, one direction) next to it. |
| C8 | "End-to-end: source and compiled x86 both stop with the same constant or both diverge, via denotations plus adequacy at both ends" | Outline §4.5; contributions | **Qualified.** Benton–Hur proves both directions for SECD; ITrees gives termination-sensitive bisimulation (Imp/Asm); Chlipala gives termination for a total source. New in combination: higher-order with recursion, closure conversion, assembly, adequacy at both ends. | State the theorem and compare; avoid "first end-to-end". |
| C9 | "Same compiler also proved in three operational styles (and a denotational one); controlled comparison" | Abstract; contributions; outline §5 | **Supported only in a narrower form, to our knowledge** (search of 2026-10-16, §1.3). Prior work does compare the cost of mechanized proofs under more than one semantic style, but on one pass or one small phase and within operational styles: Kahn–Hoffmann–Li 2025 (Agda, three operational styles on one compilation, with a lines-of-proof table) and Owens et al. 2016 (HOL4, relational versus functional big-step on one phase, 43 versus 18 lines). Danielsson 2012 and Leroy–Grall 2009 relate styles for one-pass compilers. Martin & Toal 1991 (HOL) treat one toy compiler denotationally and by SOS (abstract only). What we found no precedent for is a whole multi-pass compiler, down to assembly, proved in a denotational style and in several operational styles with the same accounting rules. | "To our knowledge, the first comparison, on a whole multi-pass compiler, of the size of mechanized correctness proofs in a denotational style and in three operational styles." Do not claim to be the first to compare semantic styles for compiler proofs; cite Kahn et al. and Owens et al. |
| C10 | "Agda `--safe`, standard library only, no postulates" | Outline §4.6 | **Engineering claim, qualified.** BahrHutton22 uses sized types and `TERMINATING` pragmas, with termination proved separately [V README; the paper itself mentions neither the pragma nor its own use of sized types, only that it presents "a step-indexed approach", p. 93:11]. Danielsson12 uses workarounds for productivity [V]. MossesCockxReus26 postulates domain constructors [A]. Whether sized types are rejected by `--safe` in current Agda is [M]. | "Fully `--safe` Agda: no postulates, no termination or productivity pragmas, no coinduction." |

The history of how these verdicts changed (the gap-closing pass, the third pass over the PDFs, the final searches) is in Part I, "Synthesis".

### 1.1 What authors say about the difficulty

Quotes for the introduction and for §4.3 and §8, grouped by the difficulty they describe. Technical statements only; each was checked against the primary text in an earlier pass (the location is given), except that the Stoy quotes come from an OCR text layer of a scan and must be checked against the printed page before use. The criteria are K2a/K2b (general recursion, and preserving *and reflecting* divergence), K1 (a relation between two denotations).

**Denotational methods did not reach general recursion in compiler proofs**

| Author, work | Quote | Where |
|---|---|---|
| Chlipala, POPL 2010 | "Our past work gives programs semantics by interpretation into Coq's strongly-normalizing logic CIC; thus, that work cannot be applied directly to Turing-complete programming languages like our source and target languages here." | §3 |
| Chlipala, POPL 2010 | "The theorem we prove in this case study ignores non-termination." | §1.1 |
| Chlipala, PLDI 2007 | Handling "effectful" features like nontermination and mutability "without first compiling to first-order form … is an interesting open problem". Domain theory "is difficult to use … in the setting of constructive type theory". | §12; §2.5 |
| Filinski, thesis 1996 | Meyer and Wand's approach "applied to all models of simply-typed λ-calculi, but did not encompass computational effects – not even nontermination." | §3.4 |
| Meyer & Wand 1985 | "The situation becomes more complicated if we study calculi in which strong normalization fails, such as the typed calculus with fixed-point operators. … it is not clear as of this writing whether this approach extends to these cases." | §15, p. 223 |
| Bahr & Hutton 2022 | The earlier calculation methodology "only considers converging behaviour"; divergence needs the partiality monad and strong bisimilarity, and a choice of how to mix induction and coinduction (guarded recursion, sized types, or step-indexing). | abstract; §2.6 |

**Proving only the forward direction; reflecting divergence is the hard part**

| Author, work | Quote | Where |
|---|---|---|
| Danvy & Nielsen 2001 | "Only lately has defunctionalization been formalized: Bell, Bellegarde, and Hook showed that it preserves types; Nielsen proved its partial correctness using denotational semantics; and Banerjee, Heintze and Riecke proved its total correctness using operational semantics." | §1.4 (Related work) |
| Pottier & Gauthier 2006 | "We believe that, because defunctionalization can be defined in an untyped setting, its semantic correctness should also be proved in such a setting"; earlier works "assumed a simply-typed calculus and carried out proofs based on logical relations". | §5 (opening of §5.1) |
| Nielsen 2000 (denotational, CPOs) | "We prove the weak correctness of the defunctionalization translation … if the original program terminates, then so does the defunctionalized one, and with the same result. Eventually, we want to prove full correctness, i.e., semantic equivalence of the two programs." | §1.3 |
| Banerjee, Heintze & Riecke 2001 | "The correctness proofs that we know of, notably those of Wand and his coauthors […], are based on special-purpose operational semantics, and prove only one direction of correctness: if the source program evaluates to a final answer, then so does the transformed program (this is often called soundness)." | §1 |
| Banerjee, Heintze & Riecke 2001 | "The reason for the lexicographic induction in the (⇒) direction is due to recursion. Indeed, we know of no other proofs of correctness (that is, both directions) for ordinary or CFA-based defunctionalization in the presence of recursion." | §4, after Theorem 5 |
| Benton & Hur 2009 | Of the direction from denotation to machine: "We will not use operational step-indexing to define the relation this way around, but an explicit admissible closure operation will play a similar rôle", because "{d \| v D^t d} is not always closed under taking limits of chains". | §4 (as recorded in Part III A8a) |
| Hur & Dreyer 2011, on Benton–Hur | "These half-operational, half-denotational relations were of necessity asymmetric … step-indexing—but only in defining one direction of approximation (in the other direction, they use an admissible closure operation)." | related work |

**Relations between two denotations at recursive or reflexive domains are non-monotone, and their existence is hard**

| Author, work | Quote | Where |
|---|---|---|
| Pitts 1993 (MFPS) | "proofs of correspondence between operational and denotational semantics (or between two different denotational semantics) often depend upon the existence of relations specified as the fixed point of non-monotonic operators." | abstract |
| Stoy 1981 | "These predicates have definitions which involve circularity and they can be rewritten as a fixed point equation. However, the function of which this set of predicates is the fixed point is not monotonic, and so the existence of such a fixed point cannot be inferred by the usual appeal to the result of Tarski". | p. 156 |
| Stoy 1981 | "The present extra complications arise in general when one tries to relate an infinitary abstract object, such as the function associated with some PL procedure by the denotational definition, with its finitary representation, such as the tree which represents the procedure in the interpreter." | p. 159 |
| Stoy 1981 | "we are not thereby claiming that no such predicates exist (that is still an open question), but merely that we do not know how to demonstrate their existence". The reason: "Formally, it is the basis of the induction which fails." | p. 163 |
| Mulmuley 1985 | On the existence proof for Stoy's order-asymmetric predicate: "The proof is undeniably complicated." The symmetric "=" version has no solution (diagonalization with λx.xx). On Reynolds's technique: it "can be used only when two domains have similar shapes or when one domain can be 'transformed' into the other domain." | CMU-CS-85-149 |
| Polak 1980/81 | His code-generation predicates are not monotone ("If l increases ϑ_S becomes smaller") and their existence is assumed: "thus we subsequently assume that the above predicates are well defined." | §IV.5.3.5, book p. 127 |
| Filinski, thesis 1996 | "Early investigations [Rey74a, ST80, Sto81] were set in a domain-theoretic framework where the main difficulties concerned reflexive domains; as a result, these methods and results were closely tied to specific semantic models." | §3.4 |
| Benton, Kennedy & Varming 2009 | For the untyped language, one "now cannot define the relation by induction on types." | §5 (Part III A8c) |
| Abramsky 1990, 1993 | The adequacy proof by domain logic is "trivial", "since analogous results in the literature have required lengthy arguments involving recursively defined inclusive predicates". | Thm 5.18; Thm 5.4.9 |
| arXiv 2208.14260 | Pitts's logical simulation relation "cannot be directly formalised in Coq for an untyped language" (it fails the strict-positivity check; the same applies in Agda). | abstract |

**Use in the introduction.** The most useful for the near-miss walk are: Chlipala 2010 and Chlipala 2007 (why denotational methods stopped at total sources), Nielsen's "weak correctness" quote, Banerjee et al.'s "we know of no other proofs … in the presence of recursion", and Stoy p. 159 (infinitary object versus finitary representation, which is the situation the approximant logical relation handles on a graph-model closure).

### 1.2 Recent publications by authors in the tier list

A web search on 2026-10-16 (snippets, abstracts and repository READMEs only; **[A]** throughout, nothing below has been read in full) for newer compiler-correctness work by the authors of the works in §2.0. Nothing found changes a tier or a verdict, but two items should be read before the paper is submitted.

| Authors | Work | What it is | Effect |
|---|---|---|---|
| **Bahr** (sole author; Hutton is not a co-author) | "Safety First: How to Safely Disregard Unsafe Behaviour in Compiler Calculations", PACMPL 10 (ICFP), Article 285, 34 pp., August 2026, doi:10.1145/3828683 [read, `related-denot/bahr-2026-safety-first.pdf`]; Agda artifact github.com/pa-ba/partial-comp-calc | Introduces *skew bisimilarity*: the compiler specification is weakened to an inequality so that unsafe source behaviour (programs the type checker rules out) can be ignored during calculation, keeping "the same strong correctness guarantees for safe source programs". Semantics is by choice trees (Chappe et al.), the common framework for source and target. It also gives "a novel calculation technique for reasoning about register machines", which "improves on existing compiler calculation techniques for register machines, which are currently limited to terminating source languages without effects" (abstract), and the "first calculation of a compiler for a typed concurrent lambda calculus that targets a register machine". Examples are toy languages in the text, with Rattus (a Fitch-style modal λ-calculus with guarded recursion) and λ-calculi with effects and concurrency in the artifact. | **Tier unchanged (K1, K3).** The semantics is a monadic (choice-tree) interpreter with environments, not a denotation; the stack and register machines keep closures (the paper's own text: the closure ⟨x, t, γ⟩, and Bahr and Hutton's `ISCLO` instruction "checks whether the top of the stack contains a closure"). Divergence is handled (non-termination is the example effect), and bisimilarity covers both directions, but only for *safe* (well-typed) programs, a relaxation of the correctness statement. The word "denotation" does not occur in the paper. A reviewer may compare "ignore unsafe behaviour" with our no-error lemmas, but it is a different device. |
| Bahr & Hutton | "Beyond Trees: Calculating Graph-Based Compilers (Functional Pearl)", PACMPL 8 (ICFP), 2024, pp. 370–394, doi:10.1145/3674638 | Calculation of compilers whose target code is a graph (jumps as edges, by higher-order abstract syntax), instead of tree-structured code; Agda artifact. | A step toward realistic targets (K4), not closure conversion. Add to the Bahr–Hutton group. |
| Bahr & Hutton | "Calculating Compilers for Concurrency", ICFP 2023; Garby, Hutton & Bahr, "Calculating Compilers Effectively", Haskell 2024 | Already in Part I §1.6. | None. |
| **Paraskevopoulou** (with the CertiCoq/CertiRocq line) | "Machine-Generated, Machine-Checked Proofs for a Verified Compiler (Experience Report)", arXiv 2602.20082 (Feb 2026); PACMPL 10 (ICFP), doi:10.1145/3828700 | Semantic preservation for the ANF pass of CertiCoq (now CertiRocq), proved in Rocq by an agentic coding assistant (Claude Code) with human guidance, adapting the earlier CPS-pass proof; about 6,000 lines in 94.5 hours in the published version. A follow-on, arXiv 2606.21167 (AI-assisted completion of CertiGC proofs), cites it. | Operational, Tier 1 (K1) unchanged. Relevant to our AI-disclosure paragraph and to any claim about proof effort: another verified-compiler paper using an AI assistant. A secondary page described the verified passes as including closure conversion, but this is not confirmed. |
| Cheng, Wu, Wang & Cao | Denotation-based Compositional Compiler Verification, TOPLAS 48(1), article 5, 2026, doi:10.1145/3797874; arXiv 2404.17297 v3 (Jan–Mar 2026); also a PLDI 2026 talk (19 June 2026, "Verified Compilation and Type Systems") | Already in Part I §1.5. No follow-up on higher-order functions or closures found; Cao's 2025 items (separation-logic C verification, eBPF) are not compiler-verification follow-ups. | None; Tier 1 (K3) unchanged. Note the PLDI 2026 presentation when citing. |
| Tune & Kavvos | "Bimodels and Biorthogonality for Abstract Machines", ICFP 2026 | Already in Part I §3. | None. |
| Bowman | A "Flat-Closure Calculus" paper listed on his home page (year not shown) | Type safety and subject reduction for a calculus that admits closure-conversion optimizations. | Type-theoretic, typed. Check the year and whether it is a semantic-correctness proof. |
| Xia, Zakowski, Zdancewic et al. | Nothing new on higher-order compiler proofs found. (Not by them: HITrees, "Higher-Order Interaction Trees", Ayyam & Sammler, arXiv 2510.14558, Oct 2025, in Lean: interaction trees extended with higher-order effects such as call/cc and parallel composition.) | HITrees may be relevant background for K1 in monadic style. | Mention in §8 if we discuss monadic denotations. |

**Closure conversion, defunctionalization and lambda lifting, 2023–2026 and earlier works not yet in the notes.** Found by searching for closure conversion, defunctionalization and lambda lifting correctness proofs by anyone (not just the authors above). Read means read to the extent stated; the rest are [A].

| Work | What it is | K1 | K2a | K2b | K3 | Tier | Notes |
|---|---|---|---|---|---|---|---|
| **Pottier & Gauthier**, "Polymorphic Typed Defunctionalization and Concretization", HOSC 19(1), 2006 (POPL 2004) [read §5, `related-denot/pottier-gauthier-2006.pdf`] | Defunctionalization as a type-preserving transformation of System F with guarded algebraic data types into itself; closure conversion "may be viewed as a particular implementation of defunctionalization". §5 proves **meaning preservation** for the untyped calculus (call-by-value, with a store of references and letrec) by a **simulation** between source and defunctionalized configurations (Lemma 5.4). | ✗ (operational) | ✓ (untyped, recursion) | ✓ (Theorem 5.5: "p ⇑ implies ⟦p⟧ ⇑. p ⇓ implies ⟦p⟧ ⇓", so termination behaviour is preserved, with determinism giving the converse) | ✓ | **1** (misses K1) | Paper proof. The closest operational counterpart: defunctionalization, untyped, divergence preserved. They argue: "because defunctionalization can be defined in an untyped setting, its semantic correctness should also be proved in such a setting", against "previous works" that "assumed a simply-typed calculus and carried out proofs based on logical relations [26, 1]" (Nielsen; Bell–Bellegarde–Hook). |
| **Danvy & Nielsen**, "Defunctionalization at Work", BRICS RS-01-23, 2001 [read the related-work paragraph] | Applications of defunctionalization (not a correctness proof). **Their summary of the proofs:** "Nielsen proved its partial correctness using denotational semantics [35, 36]; and Banerjee, Heintze and Riecke proved its total correctness using operational semantics [2]." | n/a | n/a | n/a | n/a | none | An independent statement, by a co-author of one of the two, of exactly our K1/K2b split. Quote in the introduction. |
| **Huang & Yallop**, "Defunctionalization with Dependent Types", PLDI 2023 (PACMPL 7, article 127) [read §3.4–3.5, `related-denot/huang-yallop-2023-defunctionalization-dependent-types.pdf`] | First formally specified defunctionalization for a dependently typed language (a Calculus of Constructions with labels); "soundness" is that a closed program that evaluates to a base-type value evaluates to an equivalent value after translation (a corollary of preservation of typing), plus type preservation and consistency; implementation as supplementary material. | ✗ (operational) | ✗ (dependently typed, total: every well-typed closed term reduces to a value) | n/a | ✓ | **2** | No divergence to preserve; forward direction only; paper proofs. Says it has been "difficult to adapt" CPS, closure conversion and ANF to the dependently typed setting. |
| **Fischbach & Hannan**, "Specification and Correctness of Lambda Lifting" (SAIG 2000; JFP 2003) [A] | A general formal specification of lambda lifting (Hughes and Johnsson styles) proved to preserve operational semantics. | ✗ | ? | ? | ~ (lambda lifting, not closure conversion) | **2** (tentative) | Paper. Described in Levy and Reeves. |
| **Kerneis & Chroboczek**, "Lambda-lifting and CPS conversion in an imperative language", arXiv 1202.3247, 2012 [A] | A full written proof of lambda-lifting correctness for an imperative call-by-value language with tail calls, with strengthened induction hypotheses about stores and environments. | ✗ | ✓ | ? | ~ | **2** (tentative) | Paper, operational. |
| **Levy & Reeves**, "Simple lambda lifting: Formalisation in Lean and a new efficient algorithm", FormaliSE 2026, doi:10.1145/3793656.3793692 [read the introduction and related work, `related-denot/levy-reeves-2026-lambda-lifting.pdf`] | An O(n²) lambda-lifting algorithm, proved correct against a lifting *specification* from the literature; the specification is formalised in Lean 4 and "some of the properties" are proved there; the algorithm is also tested on generated cases. Semantic preservation is Fischbach–Hannan's (operational), not re-proved. | ✗ | n/a | n/a | ~ | none | No semantic-preservation theorem of its own; the proof is that the algorithm meets the specification, and the paper does not say all of it is mechanized. A 2026 data point that lambda lifting is still being formalized. |
| **Keller & Noûs**, "Towards Metaprogramming Defunctionalization in Rocq", OlivierFest 2025 [A, abstract] | Defunctionalization as a shallow embedding in Rocq, automated by metaprogramming; "semantics and termination preservation" is a stated long-term goal. | n/a | n/a | n/a | ✓ (aim) | none | No theorem yet; mention only if we discuss mechanized defunctionalization. |
| **Brandon, Driscoll, Dai, Berkow & Milano**, "Better Defunctionalization through Lambda Set Specialization", PLDI 2023 (PACMPL 7, article 146) [read the abstract and introduction, `related-denot/brandon-lambda-set-2023.pdf`] | A *specializing* defunctionalization, formulated as a polymorphic type system that tracks the flow of function values (lambda sets), with type inference. The Isabelle/HOL proof is of "soundness and completeness of the type inference algorithm with respect to the type system" (Theorem 4.1). Evaluated on MLton, OCaml and Morphic. Semantic equivalence of the transformed program is asserted as the goal of defunctionalization in general ("a semantically-equivalent first-order representation"), but no semantics-preservation theorem is stated for the transformation itself. | n/a | n/a | n/a | ✓ (defunctionalization) | none | **Not related to our criteria**: the mechanized proof is about a type-inference algorithm, not about preservation of meaning or divergence. The word "diverg" does not occur in the paper. Mention at most as an example of a recent defunctionalization paper with a mechanized (but analysis-level) proof. |
| **Pyrosome** (Jamner et al., OOPSLA 2025, arXiv 2507.06360) | Already in §2.3: equational theories; closure conversion composed with CPS by transitivity. | ✗ | ✓ | ? | ✓ | 1 | None. |
| **Pickard**, PhD thesis "Dependent Types for Compiler Calculation", Nottingham, 2026 [read the abstract and contents, `related-denot/pickard-thesis-2026.pdf`] | Hutton's student. Calculates compilers using dependent types for typed languages (an expression language, exceptions, the simply typed λ-calculus) and extends the method with the partiality monad for a language with a non-terminating loop construct. | ✗ | ✗ (the λ-calculus is total; the non-terminating language is first-order) | n/a | ✗ | **3** | Hutton's group; no closure conversion. Supersedes Pickard–Hutton 2021 in the tier list. |

No 2025 or 2026 compiler-correctness publication was found for: Chlipala, Leroy (his latest listed item is a 2024 CoqPL note on well-founded recursion), Nielsen, Benton, Hur, Danielsson, Pitts, Wand (a December 2025 faculty page still lists compiler correctness as his area, with no new paper), Ahmed, Patterson, Myreen, Owens, Pardo and Viera. A search for Pardo, Viera and Pagano's Agda compiler work returned nothing, so their 2018 paper is the latest known. Banerjee, Heintze, Riecke, Steckler and Sullivan were not searched. These are negative results from a web search that does not index everything, not proof of absence; DBLP and Google Scholar were not queried.

### 1.3 Prior work that compares semantic styles on mechanized compiler proofs

Searched 2026-10-16 for papers that mechanize and compare more than one semantics for the same compiler (C9). The PDFs read are in `related-denot/`.

| Work | What is compared | Scale | Size data | Relation to ours |
|---|---|---|---|---|
| **Kahn, Hoffmann & Li**, "Big-Stop Semantics: Small-Step Semantics in a Big-Step Judgment", arXiv 2508.15157 (Aug 2025, v3 Oct 2025) [read §1, §6, Table 2, `related-denot/kahn-hoffmann-li-2025-big-stop.pdf`] | Soundness and completeness (convergent and divergent) of the compilation of effectful CBV PCF to a Krivine K machine, proved against **three operational semantics**: small-step, big-step and their new big-stop. Agda. | One compilation (one pass), a few lemmas | **Table 2**, non-comment non-blank lines of Agda. Soundness (convergent / divergent): big-stop 76 / 72, big-step 81 / –, small-step 88 / 84. Completeness: big-stop 32 / 72, big-step 29 / –, small-step 68 / 128. (Big-step cannot express divergence.) "We compare the sizes of proving the soundness and completeness of the K machine with respect to small-step, big-step, and big-stop semantics." | **The closest precedent for C9**: same metric (lines of Agda), same idea (one compiler, several semantic styles), also reports that small-step completeness is the costly part. But one pass, operational styles only, and the three are variations on one idea. |
| **Owens, Myreen, Kumar, Norrish, Tan et al.**, "Functional Big-Step Semantics", ESOP 2016 [read §3.4, `related-denot/owens-esop16-functional-big-step.pdf`] | Correctness of one compiler phase (`phase1`, desugaring `For` and `Dec`) in relational big-step and in functional (clocked) big-step semantics. HOL4. | One phase of a toy compiler | "our relational proof required 43 lines while the functional big-step proof required just 18 lines." Also: "In the initial version of our own CakeML project, we had two different semantics for the source language: big-step for the compiler verification and small-step for the type soundness proof, with an additional proof connecting the two semantics." | A small, deliberate comparison of two styles on one phase; also a precedent for using different semantics for different purposes in one project (cf. our mixing experiment). |
| **Knothe & Bringmann**, "Combining Small-Step and Big-Step Semantics to Verify Loop Optimizations", arXiv 2602.19868, ITP 2026 [read the abstract and introduction, `related-denot/knothe-bringmann-2026-small-and-big-step-loops.pdf`] | Uses **both** small-step semantics (for local transformations) and coinductive big-step semantics (for structural transformations, e.g. loop unswitching and unrolling) *within the same CompCert pipeline*, joined by an abstract behavioural semantics as a common interface; extends Leroy's coinductive big-step semantics to divergence with finite and infinite traces. Rocq. | Whole CompCert, new Cminor-level passes | None (no proof-size comparison). | A mixed-semantics design in one verified compiler, the idea our §7 measured and found not to pay for the pass mix we tried. Not a cost comparison. Cite in §7 and §8. |
| **Leroy & Grall**, "Coinductive big-step operational semantics", Information and Computation 207(2), 2009 [read §1, §9, `related-denot/leroy-grall-2009-coinductive-big-step.pdf`] | Coinductive big-step, small-step and a simple denotational semantics of a CBV λ-calculus, proved equivalent in Coq; the compiler to an abstract machine with closures is proved correct using the big-step semantics. | One compiler (λ-calculus to an abstract machine), proved once | None. They assert: "fairly complex, optimizing compilation passes can be proved correct (for terminating source programs) relatively easily using big-step semantics", while "compiler correctness proofs using small-step semantics can address both terminating and diverging source programs, but are more difficult even for simple, non-optimizing compilation schemes." | Relates the styles by equivalence theorems; the compiler is proved in one style. Source of the folklore claim that styles differ in proof cost. |
| **Leroy**, "Mechanized semantics: with applications to program proof and compiler verification", lecture notes, arXiv 1010.5582 (2010) [read the abstract and §4, `related-denot/leroy-2010-mechanized-semantics.pdf`] | IMP with small-step, big-step, definitional-interpreter and a simple denotational semantics, proved equivalent in Coq; the IMP-to-VM compiler (§4) is proved by forward simulation using the big-step semantics (Theorems 24 and 26). | Pedagogical, one compiler, proved once | None. Lemma 21: with a deterministic target, forward simulation implies backward simulation. | Shows that the styles are proved equivalent but the compiler proof is done in one style. Lemma 21 settles how CompCert-style proofs get reflection of divergence (forward simulation plus determinism of the target); cite it for CompCert. |
| **Martin & Toal** 1991 (HOL) | One toy imperative language and stack machine: a direct denotational treatment and an SOS treatment in two case studies [A: abstract only]. | Toy, one pass | Not known. | Only precedent found for denotational and operational on one compiler in a proof assistant; unverified whether the same compiler. |
| **Danielsson** 2012; **Bahr & Hutton** 2022 | Danielsson relates his partiality-monad semantics to Leroy–Grall's relational semantics for one compiler; Bahr–Hutton prove one compiler against an interpreter. | One pass | None. | Not comparisons of cost. |
| Danvy and co-authors (the functional correspondence); Sieczkowski–Biernacka–Biernacki (refocusing, Coq) | Mechanical derivation of abstract machines from reduction semantics and evaluators. | Derivation, not verification cost | None. | Relates styles by construction; not a comparison of proof effort. |

**Verdict for C9.** No work found mechanizes one *multi-pass* compiler to assembly under a denotational semantics and under several operational ones and compares the proof sizes. Kahn et al. (2025) is the nearest and must be cited and distinguished (one pass, three operational styles, Agda). Owens et al. (2016) and Knothe–Bringmann (2026) are the other two to cite. Remaining gap: Martin & Toal 1991 is abstract only.

---

## 2. The literature, categorized against the claims

Every paper or group of papers discussed in Parts I–III appears once, in the table for its main kind. Cells are terse: the detail and the evidence tags are in the part that discusses the work, named in the last column.

**Columns** (for §2.1 onward)

- **Mech.**: the proof assistant if the proofs are mechanized; "N" if on paper; "part." if only partly mechanized; "?" if not confirmed.
- **Source / object language**: with "1st-order" meaning no higher-order functions, "total" meaning strongly normalizing or no divergence, and "rec." meaning general recursion.
- **Closures**: how closures are treated (what bears on A2 and C3).
- **Semantics**: which languages get a denotational semantics, and of what kind.
- **A1/A2/A3**: the horn of the abstract's dilemma that a *denotational compiler proof* falls on (A1: first-order or total source; A2: target with primitive closures; A3, not yet in the abstract: only terminating programs preserved, or only one side given a denotation); "—" for works that are not denotational compiler proofs.
- **Claims**: other claims the work bears on.
- **Role**: **Counter** (contradicts the claim as stated), **Boundary** (limits the safe wording), **Nearest** (closest prior work; wording unchanged), **Ancestor** (source of a technique), **Contrast** (a different style; background), **Check** (not read far enough to classify).

### 2.0 Tiers: how many of the four core criteria a work misses

**The four core criteria.** The paper's compiler meets all four; they are what the novelty claim rests on:
- **K1. Denotational.** Every language, source, intermediate and target, has a compositional, extensional model (here a graph model), and the correctness proof of each pass relates the denotations of that pass's source and target. A definitional interpreter, a term model or an equational λ-theory does not count, and neither does a proof that uses an operational semantics for either side of a pass, even if the other side has a denotation.
- **K2a. General recursion.** The source language has general recursion, so it is Turing complete and programs can diverge.
- **K2b. Total correctness proof.** The correctness theorem preserves *and reflects* divergence: a program diverges iff its translation does (equivalently, the translation neither loses nor gains termination). A theorem for terminating programs only (Nielsen 2000), or in one direction only, does not meet it. K2b applies only when K2a holds; for a total source there is no divergence to reflect, and that work already misses K2a, so the miss is counted once.
- **K3. Closure conversion.** A pass lowers closures to first-order data (code and environment pairs, or tagged tuples). Defunctionalization counts. A target with primitive closures does not, and a first-order source has no closures to convert.

K2b is where the delay pass's reflection proof lives: in a graph model divergence is ∅, so preserving divergence is the inclusion ⟦src⟧ ⊆ ⟦tgt⟧ in one direction and reflecting it is ⟦tgt⟧ ⊆ ⟦src⟧ in the other. The near misses on K2b are therefore the works the introduction must compare most carefully (how does each treat divergence?).

**Two tie-breakers, not criteria.** Whether the work is **K4** multi-pass and ends in an assembly-level language, and **K5** mechanized. Neither is needed for the novelty claim: no prior work found meets K1, K2a, K2b and K3 together, whether or not it meets K4 or K5. They only rank works within a tier or a group.

**Tiers.** A work's tier is the number of K1, K2a, K2b, K3 it misses; ✗ and ~ (partly) both count, "?" is unchecked. Only compiler proofs get a tier; the background literature bears on K1 and on C6 and has none. Evidence is in Parts I–III. The paper outline uses this list to order the introduction's near misses and §8.

**Result of the check on 2026-10-16.** No work found meets all four. The claim is "to our knowledge, the first denotational proof of closure conversion for a source with general recursion that preserves and reflects divergence". The nearest works:
- **Nielsen 2000** meets K1, K2a and K3 (CPO denotations for source and target, a simply typed language with recursive functions, defunctionalization) but proves only the forward direction (see Part II §1, with the analysis of why that is not the delay reflection).
- **Banerjee–Heintze–Riecke 2001** prove defunctionalization correct in both directions but give the source only an operational semantics (misses K1).
- **First-order denotational compilers** (interaction trees, Cheng et al., Polak) and **Clinger/VLISP** and **Siek 2017** meet K1, K2a and K2b but miss K3: they have no closures to convert, or the target keeps closures, or the pass is not closure conversion.
- **Operational compilers** (CakeML, CertiCoq, Ahmed–Blume) meet K2a, K2b and K3 but miss K1.

The abstract's horns (first-order or strongly normalizing source; target with primitive closures) do not cover Nielsen or Banerjee et al.; the abstract needs a third horn (see the A1/A2 row in §1).

The column "Divergence" says how each work treats divergence, since K2b is the heart of the comparison.

| Tier | Misses | Work | K4 | K5 | Divergence |
|---|---|---|---|---|---|
| **1** | K2b | Nielsen 2000 | ✗ | ✗ | Forward only: `S[[p]] = up n ⇒ D[[T p]] = up n`. A diverging source says nothing about the target; no reflection. |
| **1** | K2a | Chlipala 2007 | ✓ | ✓ | None in the source (total). Coinductive traces appear only from Alloc on. |
| **1** | K3 | Clinger 1984; VLISP | ✗; ~ | ✗ | Equal meanings in one domain (Clinger), so ⊥ is covered; VLISP's machine faithfulness is one direction (machine answer ⇒ denotation). |
| **1** | K3 | Siek 2017 (inliner) | ✗ | ✓ | Equal graph-model denotations (∅ for divergence). Same-language optimization. |
| **1** | K3 | Interaction trees (Imp → Asm); Cheng et al. 2026; Polak 1980/81 (with Milner–Weyhrauch, Cohn); Vellvm, HELIX, Vélus | ~ | ✓ / part. | First-order. Termination-sensitive bisimulation (ITrees); sets of behaviours including divergence (Cheng); equal denotations (Polak, partial correctness only with respect to compiler termination). |
| **1** | K1 | Pottier & Gauthier 2004/2006 | ✗ | ✗ | Untyped defunctionalization (with a store and letrec), proved by a simulation between configurations: "p ⇑ implies ⟦p⟧ ⇑. p ⇓ implies ⟦p⟧ ⇓." Operational, paper. Their remark that untyped statements are stronger than the typed proofs by logical relations (Nielsen; Bell–Bellegarde–Hook) is quotable. |
| **1** | K1 | CakeML backend; CertiCoq | ✓; ~ | ✓ | Operational: functional big-step with clocks; step-indexed relations. Divergence preserved. |
| **1** | K1 | Banerjee–Heintze–Riecke 2001 | ✗ | ✗ | `(e,∅) ⇓ n` in the source iff in the target, by adequacy of the target's denotation and a lexicographic induction on unwindings of recursive functions and terms. Source operational. Main proof a sketch. |
| **1** | K1 | Typed and operational closure conversion whose source has recursion (Ahmed–Blume, Pilsner, Pyrosome, Wang–Nadathur, Perconti–Ahmed) | mostly ✗ | some | Step-indexed or simulation relations; K2a and K2b vary by paper. |
| **2** | K1, K3 | CompCert (and CompCertTSO, CompCertO) | ✓ | ✓ | Operational. Source C is Turing complete and first-order, so there are no closures to convert (K3). Divergence is covered by the semantic-preservation theorem over behaviours (terminating, diverging, going wrong). The reflection direction comes from forward simulation plus determinism of the target: Leroy 2010, Lemma 21 ("If P2 has deterministic semantics, then 'forward simulation for correct programs' implies 'backward simulation for correct programs'") [V, `related-denot/leroy-2010-mechanized-semantics.pdf`]. |
| **2** | K1, K3 | Benton–Hur 2009 | ✗ | ✓ | Both directions (Theorems 1 and 2): step-indexed biorthogonal relation on the machine side and an admissible closure on the denotation side. Target operational (SECD with closures). |
| **2** | K1, K2a, K3 | Huang & Yallop 2023 (defunctionalization for a dependently typed language) | ✗ | ✓ | Total source; "soundness" is preservation of base-type values (forward, terminating only); no semantic divergence question. Operational, paper. |
| **2** | K1, K3~ | Fischbach & Hannan 2000/2003; Kerneis & Chroboczek 2012 (lambda lifting) | ✗ | ✗ | Operational, paper; lambda lifting is a cousin of closure conversion (tentative). |
| **2** | K1, K3 | Bahr–Hutton 2022 (and Bahr 2026, Bahr–Hutton 2024; see §1.2); Danielsson 2012 | ✗ | ✓ | Partiality monad; strong or weak bisimilarity. Interpreters, VM keeps closures. (Bahr–Hutton 2015, 2020: converging behaviour only, so also K2b, Tier 3.) |
| **2** | K1, K2b | Chlipala 2010 | ✓ | ✓ | "ignores non-termination". |
| **2** | K1, K2b | Steckler–Wand 1994/1997 | ✗ | ✗ | Partial correctness. Untyped λ, closure conversion. |
| **2** | K1, K2a~ | Wand 1991 | ✗ | ✗ | Equational λ-theory (not extensional); tiny language. |
| **2** | K1, K3~ | Sullivan–Wand 1996; Wand–Sullivan 1997 | ✗ | ✗ | Term model with interaction as the observable (covers non-terminating interaction); lambda lifting, not closure conversion. Tentative: abstract and introduction read. |
| **2** | K2a, K3 | Morris 1973; Thatcher–Wagner–Wright 1981; Cogent; McKinna–Wright | ✗ | part. / ✓ | Simple or total languages. |
| **2** | K1, K2a | Minamide–Morrisett–Harper 1996; Bowman–Ahmed 2018; Beluga | ✗ | ✗ / ✓ | Typed, total source. |
| **2** | K1?, K3 | Rodríguez–Pagano–Fridlender 2016 | ✗ | ✓ | Krivine machine target; source semantic style and divergence not stated in the abstract. |
| **2** | K2a?, K3 | Martin & Toal 1991 | ✗ | ✓ | Toy imperative language; one pass; abstract only. |
| **3** | K1, K2a, K3 | Pickard–Hutton 2021; Pickard thesis 2026 | ✗ | ✓ | Calculated compilers for typed total languages (and a first-order non-terminating loop language, with the partiality monad); no closure conversion. |
| **3** | K1, K2b, K3 | Pardo et al. 2018; Bahr–Hutton 2015, 2020 | ✓ / ✗ | ✓ | Pardo: clocked denotations for While and a stack IL, Assm small-step; one direction (a defined result implies the assembler run), no divergence claim; first-order. |
| **3** | K1, K2a, K3 | Œuf 2018; Siek 2025 (OlivierFest) | ✓ | ✓ | Œuf: denotation for the source only, total source, explicit closures. Siek 2025: operational, first-order, total; four passes to an x86-flavored language. |

### 2.1 Denotational compiler correctness, mechanized

| Work | Mech. | Source / object language | Closures | Semantics | A1/A2 | Claims | Role | Where |
|---|---|---|---|---|---|---|---|---|
| Polak 1980/81 (Stanford thesis; LNCS 124) | part. (compiler program checked with the Stanford Pascal Verifier; semantic theory by hand) | Pascal subset, 1st-order, recursive procedures | none; display stack machine (hypothetical) | denotational, both sides (LCF-style continuations); target has no machine | A1 | C1, C6, C7 | Counter C1 (1980); ϑ predicates assumed to exist via Reynolds | I §1.9; III B4 |
| Milner–Weyhrauch 1972; Cohn 1979 (LCF; per Polak) | Edinburgh LCF | algolic language; components of a compiling algorithm | none | denotational, in LCF | A1 | C1 | Counter C1 (only through Polak's description) | I §1.9 |
| Martin & Toal 1991 | HOL | toy imperative, 1st-order, one pass | none | case 1 direct denotational; case 2 SOS (abstract only) | A1 | C1, C9 | Counter C1; C9 note | I §1.9 |
| **Chlipala 2007** | Coq | simply typed λ with nat, **total**, no recursion | closure-conversion pass (typed), closures come free from Coq's functions | denotational, every IL (Coq functions; coinductive traces from Alloc; Asm too) | A1 | C1, C3, C4, C5, C7, C8 | Counter C1; Boundary C3 and C4; Nearest | I §1.1; II §1; III B6a |
| Benton & Hur 2009 | Coq | simply typed CBV with recursion, no recursive types | none: the SECD target has closures | source domain-theoretic; target operational | A2 | C1, C4, C7, C8 | Counter C1; Boundary C4 (one pass) | I §1.2; III A8a |
| Rodríguez–Pagano–Fridlender 2016 | Coq | simply typed CBN with recursion | none: Krivine machine | source semantic style not stated in the abstract | A2 | C4 | Contrast | I §1.2 |
| Xia et al. 2020 (Interaction Trees) | Coq | Imp (while), 1st-order | n/a | monadic, coinductive denotations for Imp and Asm | A1 | C1, C7, C8 | Counter C1; Boundary C7 (Asm denotation, no machine adequacy) | I §1.4, §3 |
| Vellvm 2021; Choice Trees 2023; HELIX 2026; Kan & Ertel 2026 | Coq/Rocq | LLVM IR, numerical code, RISC-V; 1st-order | n/a | ITree semantics | A1 | C7 | Contrast (validated by tests, no independent machine) | I §1.4, §3 |
| Cheng et al. 2026 (TOPLAS) | Coq | CompCert front end: Clight → Csharpminor → Cminor, 1st-order | none | sets of behaviours (typed Kleene algebra) | A1 | C1 | Counter C1; Nearest for multi-pass | I §1.5 |
| Bourke–Jeanmaire–Pouzet 2025 (Vélus) | Rocq | Lustre dataflow, 1st-order | none | stream functions | A1 | C1 | Counter C1 | I §1.5 |
| Pardo–Gunther–Pagano–Viera 2018 | Agda | While → stack IL (LCode) → idealized assembler (Assm), 1st-order | none | clocked denotations for While and LCode; Assm small-step | A1 | C1, C7 | Counter C1; Boundary C7 | I §1.8, §3 |
| Œuf 2018 | Coq | subset of Gallina, simply typed, **total** (eliminators) | explicit closures in source; lambda lifting done in untrusted reflection, validated; heap introduction proved by simulation | source only (a function into Gallina terms); every pass proved operationally | A1 | C1, C3 | Contrast | I §1.8 |
| Cogent 2016 | Isabelle | total, linearly typed | — | shallow embedding in HOL; refinement per program | A1 | — | Contrast | I §1.8 |
| McKinna–Wright 2006 | Epigram | arithmetic expressions, total | none | total functions | A1 | — | Contrast | I §1.8 |
| Bahr–Hutton 2015, 2020, 2022, 2023; Pickard–Hutton 2021; Garby et al. 2024 | Coq / Agda | λ-calculus with arithmetic (CBV); partiality monad since 2022; dependently typed (total) and effect-handler variants | none: the VM keeps closures (`ABS` pushes one) | monadic definitional interpreter, never called denotational | A2 | C3, C10 | Contrast; Boundary C10 (sized types, `TERMINATING`) | I §1.6 |

### 2.2 Denotational (or almost denotational) compiler correctness, on paper

| Work | Mech. | Source / object language | Closures | Semantics | A1/A2 | Claims | Role | Where |
|---|---|---|---|---|---|---|---|---|
| Morris 1973; Thatcher–Wagner–Wright 1981 | N | simple languages | none | algebraic "commuting square" | A1 | C1 | Ancestor | I §1.9 |
| Clinger 1984 (Scheme 311) | N | Scheme (untyped, recursion, closures) | target `lambda` instruction builds closures | continuation semantics for source and target, one domain | A2 | C3, C4, C5 | Boundary C3 and C4 | I §1.9; III B5; `vlisp-clinger-wand.md` |
| VLISP (Guttman–Ramsdell–Wand 1995; faithfulness report M92B093) | N | Scheme → byte code | byte-code closures primitive | Clinger–Rees denotational; the byte-code machine proved faithful to it, one direction | A2 | C4, C7 | Boundary C4; Nearest paper precedent for C7 | I §1.9, §3 |
| Wand 1991 (HOAL) | N | tiny language → higher-order assembly | closure and procedure representations, inside one equational λ-theory | **not denotational** (meanings are λ-terms up to convertibility) | — | C3, C5 | Related, not a counterexample | I §1.9; III B5 |
| Wand & Oliva 1992 | N | storage representations | — | relations on terms (existence assured); the single-model approach is cited | — | C5, C6 | Ancestor | I §1.9; III B5 |
| Palsberg 1992 | N | compiler generation from action semantics | — | — | — | — | Mention generically | I §1.9 |
| Stoy 1981 | N | small language PL | interpreter closures | direct, continuation and interpreter semantics, congruence proof | — | C6 | Ancestor (inclusive predicates) | I §1.9; III B4 |
| Nielsen 2000 (BRICS RS-00-47) | N | simply typed higher-order CBV language with recursive functions (`fun f x`); defunctionalization to a first-order language | defunctionalization (whole environment stored in tagged values) | **denotational on both sides** (CPOs, least fixed points); logical relations; **weak correctness: only terminating programs** [V, `related-denot/nielsen-2000.pdf`] | A3 | C3 | **Tier 1** (misses K2b); the nearest denotational closure-conversion-like proof | II §1 |
| Banerjee–Heintze–Riecke 2001 | N | PCF with control-flow types (simply typed CBV, recursion) → first-order language | defunctionalization (tagged tuples plus `apply`), CFA-based; also flow-based inlining | source operational (natural semantics); **denotational semantics for the first-order target only**; correctness is "iff" on final answers, by finite unwindings [V, `related-denot/Banerjee-Heintze-Riecke.pdf`] | — | C3 | Contrast (Tier 3) | II §1 |
| Steckler–Wand 1997 (TOPLAS; from Wand–Steckler, POPL 1994); Steckler 1994 | N | untyped λ with integers, booleans, conditionals; lightweight closure conversion | closure conversion (lightweight closures, flow analysis) | **operational**: big-step evaluation preserving occurrence information, an equational "weak equivalence", a commuting-diagram correctness theorem; partial correctness ("we do not assume termination") [V, `related-denot/steckler-wand-1997.pdf`] | — | C3 | Contrast (Tier 4) | II §1; III B6c |
| Wand–Sullivan 1997 (POPL); Sullivan–Wand 1996 (manuscript, "Incremental Lambda Lifting") | N | Scheme; assignment elimination and incremental lambda lifting | lambda lifting: a source-to-source change of scope that reduces closure allocation (not lowering of closures) | "denotational semantics in an operationally-based term model in which interaction is the basic observable" (a term model, so not an extensional model; the authors call it "almost-denotational"); covers non-terminating interaction [V abstracts and introductions, `related-denot/Wand-Sullivan-1997.pdf`, `related-denot/Sullivan-Wand-1996.pdf`; proofs not read] | — | C3 | Contrast (Tier 2, tentative) | II §1 |
| Ghica 2007; GoS IV 2011 | N | SCI-typed higher-order language → circuits | — | game semantics / geometry of interaction | — | — | Contrast | I §4 |
| CompCertO (Koenig & Shao 2021) | Coq | C and assembly | — | game-inspired operational interfaces | — | — | Contrast | I §4 |

### 2.3 Operational (or type-theoretic) compiler correctness, and closure conversion in general

All of these prove their compilers with operational semantics, simulations, logical relations over terms, or type preservation. They support the abstract's opening sentence (verified compilers are almost entirely operational) and bear on C3 and C9 only as contrast. None is denotational. "CC" means closure conversion.

| Work | Mech. | Source language | Closure conversion | Proof style | Claims | Role | Where |
|---|---|---|---|---|---|---|---|
| **CompCert** (Leroy 2006, 2009; and CompCertTSO) | Coq | C (Clight and below): Turing complete, first-order | none: no closures to convert | operational; simulation proofs through about twenty passes down to assembly | C9 | **Tier 2** (misses K1 and K3); the most famous compiler-correctness proof, so it must be named | I §1.10 |
| CakeML backend (Owens et al. 2017; Tan et al. 2019) | HOL4 | typed ML; CC on untyped ClosLang | yes | functional big-step with clocks | C9 | Contrast | I §1.10; II §3 |
| CertiCoq (Paraskevopoulou–Appel 2019; –Li–Appel 2021) | Coq | untyped CPS λ ILs | yes (flat) | step-indexed LR, composed across passes | C3 | Contrast; the untyped mechanized CC line | II §3 |
| Pilsner 2015; Hur–Dreyer 2011 | Coq | ML-like imperative HO language; System F-like with recursive types | multi-pass (Pilsner) | parametric simulations; Kripke step-indexed LR | — | Contrast | II §3; III A8d |
| Benton–Hur 2010 | (tech report) | polymorphic CBV with recursion | — | realizability; source operational | — | Contrast | I §1.3; III A8b |
| Chlipala 2010 | Coq | untyped mini-ML with references and exceptions | yes | big-step, closure heap, syntactic compatibility; terminating programs only | C3 | Contrast; says denotational methods do not reach Turing-complete languages | II §3; III B6b |
| Danielsson 2012; Leroy–Grall 2009 | Agda; Coq | untyped λ → stack VM | no: VM closure is atomic | partiality-monad interpreter (not denotational); coinductive big-step | C9 | Precedents for several operational styles on one pass | I §1.7; II §3 |
| Wang–Nadathur 2016 | Abella | typed functional | typed CC, hoisting | step-indexed LR | — | Contrast | II §3 |
| Savary Bélanger–Monnier–Pientka 2013/2015 | Beluga | STLC | yes | type preservation only | — | Contrast | II §3 |
| Pyrosome (Jamner et al. 2025) | Coq | System F with references; recursive functions | yes | equational theories | — | Contrast | I §1.10; II §3 |
| Brack (Lasnier–Yallop–Myreen 2026) | HOL4 | Scheme with first-class continuations → CakeML | CPS | operational | — | Contrast | I §1.10 |
| Okuma–Minamide 2003 | Isabelle | compiler specification with a CC phase | yes | extent of the semantic proof unconfirmed | — | Check | II §3 |
| Minamide–Morrisett–Harper 1996 | N | typed λ (simple, polymorphic) | typed CC, existentials | operational, type-indexed LR | C3 | Contrast | II §2; III B6c |
| Ahmed–Blume 2008; New–Bowman–Ahmed 2016; Bowman–Ahmed 2018 | N | System F with existential and recursive types; CC | typed CC, full abstraction | step-indexed LR plus back-translation; model of CC-CC in CC | — | Contrast | II §2 |
| Perconti–Ahmed 2014; Mates–Perconti–Ahmed 2019; Patterson–Ahmed 2019 | ? | typed, multi-language | typed CC | multi-language LRs; a framework for compiler-correctness statements | C8 | Contrast; Patterson–Ahmed useful for stating the end theorem | II §2 |
| Sullivan–Downen–Ariola 2023; Sullivan 2023 thesis | ? | call-by-push-value | CC as β/η steps with delayed environments | equational theory plus abstract machine | — | Contrast; related to the delay pass | II §1 |
| Morrisett et al. 1999 (TAL); Guillemette–Monnier 2007 | N; Haskell (GADTs) | System F | type-preserving CC | typing | — | Contrast | II §2 |
| Hannan 1995 | LF/Elf (deductive systems) | closure conversion as type systems | yes | no semantic correctness proof | — | Contrast | II §1 |
| Biernacki–Polesiuk 2025 | ? | untyped CBV with call/cc | no (CPS translation) | untyped step-indexed LR defined by eliminators | C6 | Contrast; nearest operational analogue of the approximant relation | II §4 |
| Siek 2025 ("Verified Nanopasses for Compiling Conditionals") | Agda | let, arithmetic, conditionals → x86-flavored RTL; 1st-order, total | none | definitional interpreters and big-step relations | — | Precursor for the back end, not for the graph-model method | I §1.10 |

### 2.4 Graph, filter and elementary models of the λ-calculus, and their mechanizations

| Work | Mech. | What it is | Compiler? | Claims | Role | Where |
|---|---|---|---|---|---|---|
| Plotkin 1972/1993; Scott 1976; Engeler 1981; Longo 1983 | N | graph and set-theoretical models | no | C2 | Background (our model is Engeler/Plotkin style) | II §6; III B7 |
| Barendregt–Coppo–Dezani 1983; Coppo–Dezani–Venneri 1981; Krivine 1993 | N | filter models and intersection types | no | C2 | Background | II §6; III A5 |
| **Siek 2017** (arXiv 1707.03762; Isabelle) | Isabelle | graph model for CBV λ; soundness/adequacy; polyvariant inliner proved by equal denotations | inliner only (same language) | C2 | **Boundary C2**: the only prior mechanized graph-model transformation proof | I §2; III A6 |
| Siek, AFP "Declarative Semantics for Functional Languages" | Isabelle | four views of the semantics; inliner, semantic type soundness, references | no | C2 | Nearest | I §2 |
| PLFA part 3 (Siek et al.) | Agda | filter-style model of the untyped CBN λ; compositionality, soundness, adequacy | no | C2, C7 | Nearest (Agda predecessor) | I §2; III A7 |
| Siek 2019 (arXiv 1906.09709) | N | BCD subtyping without transitivity; "filter models for compiler verification" as a stated programme | no | C2 | Background | I §2; II §7 |
| Mosses 2025 (Scheme workshop; R5RS in Agda) | Agda (shallow embedding) | denotational semantics of Scheme | **no** | C2 | Contrast | I §2 |
| Mosses–Cockx–Reus 2026 (MFPS) | Agda with postulates | Scott–Strachey domains in Agda | **no** | C2, C10 | Contrast | I §2 |
| Benton–Kennedy–Varming 2009 (and the BBKV draft) | Coq | ω-cpos, inverse limits; adequacy for typed and untyped CBV | no | C2 | Contrast (domain theory, not graph model) | I §1.3; III A8c |
| de Jong–Escardó (Scott's D∞ in TypeTopology) | Agda | inverse limits, algebraic domains | no | C2 | Contrast | I §2; II §6 |
| Garlene 2026 (guarded recursion in Lean) | Lean | adequacy for λ with fixpoints | no | — | Contrast | I §2 |
| Laurent (Coq BCD transitivity); Larchey-Wendling (constructive λ, intersection systems) | Coq | intersection-type mechanizations | no | C2 | Contrast | I §2 |
| Ehrhard 2020 | N | non-idempotent intersection types as an indexed logic over a relational model | no | C6 | Ancestor of "relations indexed by finite observations" | II §6 |
| Abramsky 1991 (Domain Theory in Logical Form) | N | formulas as compact elements; logic vs model | no | C6 | Background | III A4c |

### 2.5 Adequacy: a denotation against syntax, an interpreter or a machine

| Work | Mech. | Language | What is related | Direction | Claims | Role | Where |
|---|---|---|---|---|---|---|---|
| Winskel 1993, §13.4 and §13.9 | N | recursive types, eager and lazy | information-system tokens vs canonical forms, by recursion on token size | convergence | C6 | Ancestor of finite-element indexing (adequacy only) | III A1 |
| Martin-Löf 1983 | N | untyped program forms of type theory | formal neighbourhoods vs programs, inductive | denotational ⊆ operational neighbourhood | C6 | Ancestor (origin of the finite-element method) | III A2 |
| Abramsky 1990 (lazy λ); Abramsky–Ong 1993 | N | lazy λ-calculus | domain-logic formulas vs terms in a transition system | both (Thm 5.4.9) | C6 | Ancestor | III A4a, A4b |
| Pitts 1993/1994 (MFPS); 1996 §5 | N | untyped CBV; recursive types | ◁ ⊆ D × Prog via minimal invariance | adequacy | C6 | Ancestor (the mixed-fixed-point method) | III A3, B1, B2 |
| Siek 2017 §5.1 | Isabelle | graph model for CBV | element-indexed G: a finite value vs closures | soundness (adequacy) | C6, C7 | Ancestor of the element-indexed relation | III A6 |
| PLFA "Adequacy" | Agda | untyped CBN | 𝕍/𝔼: a finite Value vs closures, by recursion on Value | adequacy | C7 | Ancestor | III A7 |
| Tune & Kavvos 2026 (ICFP) | Agda | CBPV, typed and **total**; CK/CEK machines | set-theoretic bimodel vs machine run | one direction | C7 | **Boundary C7** (mechanized adequacy against CK/CEK; no assembly, no divergence) | I §3 |
| Egidi–Honsell–Ronchi Della Rocca 1992 | N | ISWIM/SECD vs a filter model | operational vs denotational vs logical descriptions | method unseen | C7 | Check | III A5 |
| RockSalt / bigrammar decoder DSL | Coq | x86 *decoder* DSL | denotational vs operational semantics of the DSL | — | C7 | Contrast (not program execution) | I §3 |
| Guarded Interaction Trees (Frumin et al. 2024) | Iris/Coq | modular denotational semantics | adequacy, interoperability | — | C7 | Contrast (no compiler) | II §5 |
| Møgelberg–Paviotti 2016/2019; Giovannini–New 2024 | N / Agda | synthetic guarded domain theory; recursive types | guarded-recursive LR for adequacy; denotations that count steps | adequacy | C6 | Alternative to the finite-observation relation; no CC result found | II §5 |
| Capretta 2005; Danielsson 2012 (partiality monad) | Coq; Agda | denotations with steps | delay monad | — | C6 | Alternative (third way to discharge ▷) | II §5 |
| (Benton–Hur 2009; Pardo et al. 2018; VLISP faithfulness) | | | listed in §2.1 and §2.2 | | C7 | | |

### 2.6 Relations between two denotations, and relations over recursive domains

All of these bear on C6. None is indexed by a finite approximation on one side with an arbitrary element on the other.

| Work | Mech. | What is related | Indexing | Notes | Role | Where |
|---|---|---|---|---|---|---|
| Reynolds 1974 | N | direct vs continuation semantics (two reflexive domains) | stages of both domains, intersected | the closest structural precedent (tower θ₀ = ⊤, θₙ₊₁ = B(θₙ)) | **Ancestor** | III B3 |
| Milne 1973; Milne–Strachey 1976; Plotkin 1973 | N | inclusive predicates (the stage method) | inverse-limit stages | primary texts of Milne–Strachey not read | Ancestor | III B1, B4 |
| Stoy 1981 | N | direct vs continuation (symmetric); continuation vs interpreter (order-asymmetric) | approximation domains, conjunction | see §2.2 | Ancestor | III B4 |
| Mulmuley 1985 (CMU-CS-85-149); 1987 | N | two semantics; "weaker-than" predicates; existence theory | finitary projections in a universal domain | the 1987 book is unread | Ancestor | III B4 |
| Meyer–Wand 1985 | N | direct meaning vs meaning of the CPS transform | types (λ-definable retractions, "concrete invariant") | typed, no fixed points | Contrast | III B5 |
| Filinski 1996 thesis; Filinski 2007 | N | two monadic interpretations of one metalanguage with recursive types | types; Pitts-style existence (Thm 39) | symmetric; no finite elements | Contrast | III B5 |
| Filinski–Støvring 2007 | N | two models of backtracking | rigid induction | body unread | Contrast | III B5 |
| Pitts 1996, §3, §4 (Thm 4.16), §6 | N | invariant relations; homogeneous co-induction | minimal invariant | names the heterogeneous B case but does not work it out | Ancestor | III B1 |
| Birkedal–Harper 1999; Crary–Harper 2007 | N | syntactic minimal invariance (operational) | types | includes a relational CPS proof | Contrast | II §4 |
| Appel–McAllester 2001; Ahmed 2006; Dreyer–Ahmed–Birkedal 2009/2011; Pitts 2010 (tutorial) | N | step-indexed relations (operational) | step index | the step-indexing route | Contrast | II §4 |
| Coq paper arXiv 2208.14260 (Core Erlang) | Coq | Pitts's relation for an untyped CBV language | — | reports that Pitts-style relations fail Coq's positivity check; Agda has the same check | Contrast | II §4 |
| Smyth–Plotkin 1982; Abadi–Plotkin 1990 | N | recursive domain equations; PER model | — | recommended in the blog comments | Background | II §4 |
| Sieber 1992; O'Hearn–Riecke 1995; Jung–Tiuryn 1993; Jung–Stoughton 1993; Loader 2001; Stoughton 1993 | N | "finitary" in the sense of finite arity or finite types (PCF) | — | name check: the word "finitary" is overloaded (§ Name check in Part III) | Naming risk only | III Name check |
| Siek blog 2023; TYPES thread 2018 | — | the problem statement for closure conversion with graph models | — | comments suggest logical relations, Minamide–Morrisett–Harper, Pitts | Background | II §1 |

---

## 3. Local PDFs

`related-denot/` (repository root, not in git) holds the PDFs of the papers that are hard to find. Everything below was read in the third pass of the novelty search (2026-10-15) unless noted.

| File | Paper | Used for | Where discussed |
|---|---|---|---|
| `3-540-10886-6_1.pdf` … `_5.pdf` | Polak, *Compiler Specification and Verification*, LNCS 124, 1981 (one PDF per chapter, I–V) | C1, C6, C7: first denotational, partly machine-checked compiler proof | I §1.9; III B4 |
| `abramsky-1993.pdf` | Abramsky & Ong, "Full Abstraction in the Lazy Lambda Calculus", Inf. & Comp. 105, 1993 | adequacy by the domain logic (Thm 5.4.9); image-only scan, read page by page | III A4b |
| `bahr-hutton-2022.pdf` | Bahr & Hutton, "Monadic Compiler Calculation", ICFP 2022 | C1, C3, C10: divergence in calculated compilers; the VM keeps closures | I §1.6 |
| `clinger-1984.pdf` | Clinger, "The Scheme 311 Compiler", LFP 1984 | A2, C3, C4: target with closure-building `lambda` | I §1.9; III B5; `vlisp-clinger-wand.md` |
| `filinski-2007.pdf` | Filinski, "On the relations between monadic semantics", TCS 2007 | C6: Pitts-style relations between two interpretations | III B5 |
| `meyer-wand-1985.pdf` | Meyer & Wand, "Continuation Semantics in Typed Lambda-Calculi (Summary)", 1985 | C6: retractions instead of inclusive predicates | III B5 |
| `pardo-2018.pdf` | Pardo et al., "An Internalist Approach to Correct-by-Construction Compilers", PPDP 2018 | C1, C7: Agda, While → stack IL → assembler | I §1.8, §3 |
| `Banerjee-Heintze-Riecke.pdf` | Banerjee, Heintze & Riecke, "Design and Correctness of Program Transformations Based on Control-Flow Analysis", TACS 2001 | C3: defunctionalization, denotational target only | II §1 |
| `Wand-POPL-1994.pdf` | Wand & Steckler, "Selective and Lightweight Closure Conversion", POPL 1994 | C3: operational, untyped | II §1; III B6c |
| `siek-2017.pdf` | Siek, "Revisiting Elementary Denotational Semantics", arXiv 1707.03762 (v4) | C2, C6, K2: the language is the untyped λ-calculus with integers, general recursion via Y; the inliner (§6) | I §2; III A6 |
| `steckler-wand-1997.pdf` | Steckler & Wand, "Lightweight Closure Conversion", TOPLAS 19(1), 1997 (converted from the author's PostScript) | C3: operational, paper, untyped λ | II §1; III B6c |
| `nielsen-2000.pdf` | Nielsen, "A Denotational Investigation of Defunctionalization", BRICS RS-00-47, 2000 | K1, K2a, K3: denotational, higher-order, recursion, defunctionalization; misses K2b (terminating programs only, A3) | II §1 |
| `Wand-Sullivan-1997.pdf`, `Sullivan-Wand-1996.pdf` | Wand & Sullivan, "Denotational Semantics Using an Operationally-Based Term Model", POPL 1997; Sullivan & Wand, "Incremental Lambda Lifting", 1996 (converted from the authors' PostScript) | K1: a term model, not an extensional model | II §1 |
| `bahr-2026-safety-first.pdf` | Bahr, "Safety First: How to Safely Disregard Unsafe Behaviour in Compiler Calculations", ICFP 2026 | Newest calculated-compiler work; K1, K3 | I; §1.2 |
| `pickard-thesis-2026.pdf` | Pickard, "Dependent Types for Compiler Calculation", Nottingham PhD thesis, 2026 | Hutton's group; Tier 3 | §1.2 |
| `pottier-gauthier-2006.pdf` | Pottier & Gauthier, "Polymorphic Typed Defunctionalization and Concretization", HOSC 2006 | Operational meaning preservation for untyped defunctionalization, divergence preserved; Tier 1 | §1.2 |
| `huang-yallop-2023-defunctionalization-dependent-types.pdf` | Huang & Yallop, "Defunctionalization with Dependent Types", PLDI 2023 | Defunctionalization for a total, dependently typed language; Tier 2 | §1.2 |
| `danvy-nielsen-2001.pdf` | Danvy & Nielsen, "Defunctionalization at Work", BRICS RS-01-23, 2001 | Their summary of Nielsen's and Banerjee et al.'s proofs | §1.1 |
| `brandon-lambda-set-2023.pdf` | Brandon et al., "Better Defunctionalization through Lambda Set Specialization", PLDI 2023 | Mechanized proof is about type inference, not semantic preservation; unrelated to the criteria | §1.2 |
| `levy-reeves-2026-lambda-lifting.pdf` | Levy & Reeves, "Simple Lambda Lifting: Formalisation in Lean and a new efficient algorithm", FormaliSE 2026 | Lambda lifting against a specification | §1.2 |
| `kahn-hoffmann-li-2025-big-stop.pdf` | Kahn, Hoffmann & Li, "Big-Stop Semantics", arXiv 2508.15157 (v3) | C9: Table 2 compares Agda proof sizes under three operational semantics for one compilation | §1.3 |
| `owens-esop16-functional-big-step.pdf` | Owens et al., "Functional Big-Step Semantics", ESOP 2016 | C9: 43 versus 18 lines for one phase | §1.3 |
| `knothe-bringmann-2026-small-and-big-step-loops.pdf` | Knothe & Bringmann, "Combining Small-Step and Big-Step Semantics to Verify Loop Optimizations", arXiv 2602.19868 | Mixed semantics in CompCert | §1.3 |
| `leroy-grall-2009-coinductive-big-step.pdf` | Leroy & Grall, "Coinductive big-step operational semantics", 2009 (arXiv 0808.0586) | Styles proved equivalent; compiler proved once | §1.3 |
| `domains-for-denotational.pdf` | Scott, "Domains for denotational semantics", ICALP 1982, LNCS 140 (scan, OCR text) | Consistency precedent: information systems (§2); a pairwise-consistent graph-fragment example (§2, third example: (a_i,b_i) consistent iff a_i = a_j ⇒ b_i = b_j); the model of D = A + (D → D) whose function data objects are pairs (u, v) of consistent sets, consistent under the subset rule (§7, clause (7)); "there are many reasons for retaining the consistency concept throughout" | §3 of the paper (Consistency) |
| `gunter-scott-1990-semantic-domains.pdf` | Gunter & Scott, "Semantic Domains", Handbook of TCS vol. B, 1990 | Checked: order-theoretic, no consistency predicate; not a consistency precedent. Authors are Gunter and Scott only (bib fixed) | — |
| `plotkin-1978-t-omega-universal-domain.pdf` | Plotkin, "Tω as a universal domain", JCSS 17, 1978 | Coherent (pairwise-consistent) domains, p. 210 | §3 of the paper (Consistency) |
| `larsen-winskel-1984-information-systems-TR51.pdf` | Larsen & Winskel, "Using information systems to solve recursive domain equations effectively", 1984 (Cambridge TR 51, scan) | Function-space consistency rule of information systems, Def. 4.18 | §3 of the paper (Consistency) |
| `schwichtenberg-2006-recursion-partial-continuous-functionals.pdf` | Schwichtenberg, "Recursion on the partial continuous functionals", Logic Colloquium '05, 2006 | Coherent information systems; pairwise function-space rule (Def. 2.4), matching ours | §3 of the paper (Consistency) |
| `karadais-2013-thesis-partial-computable-functionals.pdf`, `karadais-2008-cie-acis-slides.pdf` | Karádais, PhD thesis, LMU 2013; CiE 2008 slides | The pairwise rule in our exact notation, (U,a) ≍ (V,b) iff U ≍ V → a ≍ b (thesis §1.1 p. 10) | — |
| `girard-taylor-lafont-1989-proofs-and-types.pdf` | Girard, Lafont & Taylor, *Proofs and Types*, 1989 | Coherence spaces; stable function space (§8.5.2) adds a stability clause that ours lacks | — |
| `plotkin-1993-set-theoretical-models-lambda.pdf` | Plotkin, "Set-theoretical and other elementary models of the λ-calculus", TCS 121, 1993 (preprint) | Graph models; cites applicative information systems | — |
| `abramsky-1991-domain-theory-logical-form.pdf` | Abramsky, "Domain theory in logical form", APAL 51, 1991 | Its C predicate is coprimeness, not consistency | — |
| `bucciarelli-carraro-ehrhard-salibra-2010-linear-information-systems.pdf` | Bucciarelli et al., "On linear information systems", EPTCS 22, 2010 | Points to Berline's webbed models with pairwise coherence | — |
| `leroy-2010-mechanized-semantics.pdf` | Leroy, "Mechanized semantics", lecture notes, arXiv 1010.5582 | Lemma 21 (forward simulation + determinism) | §1.3 |
| `benton-birkedal-kennedy-varming-formalizing-domains.pdf` | Benton, Birkedal, Kennedy & Varming, "Formalizing Domains, Ultrametric Spaces and Semantics of Programming Languages", manuscript (MSCS draft, c. 2010) | Size of mechanized domain theory: "Categories and the domain theory library, including the theory of recursive domain equations, total around 4400 lines" of Coq; the simply typed language's soundness and adequacy about 1000 more, the unityped language about 1200 | III A8c; cited in the introduction |
| `rel-prop-domains.pdf` | Pitts, "Relational Properties of Domains", Information and Computation 127(2):66–90, 1996 | Theorem 4.16 (existence of invariant relations); §5 adequacy; §6 induction and co-induction; p. 68 names relations between two denotational semantics (Reynolds 1974) as an application, not worked out | III B1; cited in the introduction |
| `stoy-1981.pdf` | Stoy, "The Congruence of Two Programming Language Definitions", TCS 1981 | C6: inclusive predicates; OCR of a scan, so quotes need checking against the printed page | I §1.9; III B4 |
| `milner-1978-type-polymorphism.pdf` | Milner, "A Theory of Type Polymorphism in Programming", JCSS 17, 1978 (2026-10-22) | Universal domain of tagged values: V = B₀ + B₁ + ⋯ + F + W, F = V → V, W = {·} ("wrong"), p. 357 | §5.5 of the paper (threats: universal domain) |
| `benton-kennedy-varming-2009-domain-theory-coq.pdf` | Benton, Kennedy & Varming, "Some Domain Theory and Denotational Semantics in Coq", TPHOLs 2009 (2026-10-22) | Typed language: a domain per type (`SemTy`, by recursion on types, §3); untyped language in D ≃ (nat + (D →c D))⊥ (§5), relations by Pitts's invariant-relation method | §5.5 of the paper (threats: universal domain) |
| `dockins-2014-formalized-domain-theory-coq.pdf` | Dockins, "Formalized, Effective Domain Theory in Coq", ITP 2014, LNCS 8558 (2026-10-22) | Profinite domains in Coq, bilimits for recursive domain equations (§7); soundness and adequacy for simply typed SKI and λ-calculus with and without fixpoints (§8); a domain per type (see the note below the table) | §5.5 of the paper (threats: universal domain) |
| `macqueen-plotkin-sethi-1986-ideal-model.pdf` | MacQueen, Plotkin & Sethi, "An Ideal Model for Recursive Polymorphic Types", Inf. & Control 71, 1986 (2026-10-22) | Universal domain V ≅ T + N + (V→V) + V×V + V+V + {wrong} (eq. 2.1); types, including recursive, universal and existential ones, as ideals of V (§§3–5) | §5.5 of the paper (threats: universal domain) |
| `tune-2026.pdf` | Tune & Kavvos, "Bimodels and Biorthogonality for Abstract Machines", ICFP 2026 | C7: mechanized adequacy against CK/CEK machines | I §3 |

Papers read from other sources (author or publisher pages, arXiv, Zenodo, a MITRE report found through the Wayback Machine) are noted in the part that discusses them.

For Dockins 2014 (local, below), the interpretation of types is not spelled out in the paper; it was checked in the library's source (port at https://github.com/lastland/DomainTheory, `st_lam_fix.v`, 2026-10-22): `tydom` gives a domain per type by recursion on types (flat booleans, lifted function spaces), and the languages have no recursive types.

---

# Part I. Compiler correctness with denotational semantics, graph-model mechanizations, and adequacy for assembly

(The novelty search of 2026-10-15; formerly `novelty-literature.md`.)

Compiled 2026-10-15. Read-only literature search. A second pass the same day closed most of the gaps listed at the end (Polak 1980/81, the VLISP faithfulness report, Bahr–Hutton 2022, Œuf, Pardo et al., Siek 2025, Siek 2017's wording, Mosses 2025/2026, game semantics) and ran the final searches; the entries below record what was found and where. A third pass read the PDFs the author placed in `related-denot/` (Polak's LNCS 124 book, Clinger 1984, Stoy 1981, Meyer–Wand 1985, Filinski 2007, Bahr–Hutton 2022, Pardo et al. 2018, Tune–Kavvos 2026; text extracted with pdftotext); `abramsky-1993.pdf` has no text layer and was read later page by page as images: its adequacy proof (Theorem 5.4.9, p. 206) is the LLC domain-logic method [V], see Part III A4b.

## How each claim was checked

- **[V]** Verified in this session from the primary source (PDF text or the author's own page). Quotes are verbatim.
- **[V-notes]** Verified in the repo's earlier notes. These are Part III (as of commit f989398) and Part II (as of mu-main). Both marked the item as read from the primary source. I did not re-read it this session.
- **[A]** Checked only from an abstract, the publisher or arXiv metadata, Crossref, a README, or search snippets.
- **[M]** From memory, or secondary only. **Do not cite without checking.**

BibTeX metadata (authors, title, venue, pages, DOI) is from Crossref unless the entry says otherwise.

---

## (1) Compiler correctness with denotational semantics (source, target, or intermediate languages)

### 1.1 Chlipala, PLDI 2007: the closest mechanized precedent

```bibtex
@inproceedings{Chlipala07,
  author={Adam Chlipala}, title={A Certified Type-Preserving Compiler from Lambda Calculus to Assembly Language},
  booktitle={PLDI}, pages={54--65}, year={2007}, doi={10.1145/1250734.1250742}}
```

- **What it is [V].** A compiler from the simply-typed λ-calculus (types `N | τ→τ`, with no recursion) to an "idealized assembly language". It is checked in Coq.
- **Pipeline [V].** Source → Linear → CPS → CC (closure conversion) → Alloc → Flat → Asm.
- **Semantics [V].**
  - "Semantics preservation is proved based on denotational semantics assigned to the intermediate languages."
  - "For this and all our other languages, we opted to use denotational semantics."
  - Source denotations are Coq sets and functions.
  - From Alloc onward, programs denote co-inductive traces: "an infinite sequence of stars … will be the denotation of a non-terminating program".
  - **Asm's semantics is itself a denotation** (§2.7: "We re-use the trace-based approach"). Asm is parametric in an unverified runtime system and garbage collector.
- **Contributions as stated [V].**
  - "first total correctness proof of an entire type-preserving compiler".
  - "gives the proof using denotational semantics, in contrast to the typical use of operational semantics in related work".
- **Proof method [V-notes].** Each pass is proved by type-indexed logical relations between the source and target denotations, including CPS→CC.
- **Handles:** closures and closure conversion, yes. General recursion or divergence in the source, no (total). Adequacy of the Asm denotation against a machine, none (there is no separate machine). The result is end-to-end.
- **Compared with ours:** same overall shape (a denotation for every intermediate language, closure conversion, down to assembly). But the source is total and simply typed, the semantics is Coq functions rather than a graph model, the per-pass statements are logical relations rather than equality, and there is no machine adequacy.

### 1.2 Benton & Hur, ICFP 2009

```bibtex
@inproceedings{BentonHur09,
  author={Nick Benton and Chung-Kil Hur}, title={Biorthogonality, Step-Indexing and Compiler Correctness},
  booktitle={ICFP}, pages={97--108}, year={2009}, doi={10.1145/1596550.1596567}}
```

- **Abstract [V].** "We define logical relations between the denotational semantics of a simply typed functional language with recursion and the operational behaviour of low-level programs in a variant SECD machine … The results have been formalized in the Coq proof assistant."
- **Semantics [V].** The source (PCFv) gets a cpo-based, domain-theoretic semantics, built on the BKV09 Coq library. The target is operational (an SECD variant with closures in its values: "a closure containing an environment and some code, a recursive closure").
- **Proof method [V-notes].** Two asymmetric relations: a step-indexed one on the machine side, and the other closed under an admissible closure operation. Theorems 1 and 2 give the two directions.
- **Size [V].** About 4000 lines, "not including the library for domain theory".
- **Handles:** recursion and divergence, yes. Closure conversion, no (the SECD machine has closures). Single pass. No recursive types.
- **Related-work remarks [V].**
  - On VLISP: "relating a denotational semantics to, ultimately, real machine code … though the proofs were not mechanized".
  - On Chlipala: "the source language is total and so can be given an elementary semantics in Sets".
- **Compared with ours:** a mechanized denotational source semantics with general recursion compiled to a low-level machine. But it is one pass, has no closure conversion, uses domain theory rather than a graph model, and the target side is operational.
- **Follow-up [A, abstract via OpenAlex].** Rodríguez, Pagano & Fridlender, "Proving Correctness of a Compiler Using Step-indexed Logical Relations", ENTCS 2016, doi:10.1016/j.entcs.2016.06.013: "we prove the correctness of a compiler for a call-by-name language using step-indexed logical relations and biorthogonality. The source language is an extension of the simply typed lambda-calculus with recursion, and the target language is an extension of the Krivine abstract machine. We formalized the proof in the Coq proof assistant." Whether the source side is denotational (as in Benton–Hur) is not stated in the abstract. One pass, a Krivine machine target (closures in the machine), so it does not affect C3/C4/C7.

### 1.3 Benton, Kennedy & Varming, TPHOLs 2009; Benton & Hur 2010; Hur & Dreyer 2011

```bibtex
@inproceedings{BKV09, author={Nick Benton and Andrew Kennedy and Carsten Varming},
  title={Some Domain Theory and Denotational Semantics in {Coq}}, booktitle={TPHOLs}, series={LNCS}, volume={5674},
  pages={115--130}, year={2009}, doi={10.1007/978-3-642-03359-9_10}}
@techreport{BentonHur10, author={Nick Benton and Chung-Kil Hur},
  title={Realizability and Compositional Compiler Correctness for a Polymorphic Language},
  institution={Microsoft Research}, number={MSR-TR-2010-62}, year={2010}}
@inproceedings{HurDreyer11, author={Chung-Kil Hur and Derek Dreyer}, title={A {Kripke} Logical Relation Between {ML} and Assembly},
  booktitle={POPL}, pages={133--146}, year={2011}, doi={10.1145/1926385.1926402}}
```

- **BKV09 [V-notes].**
  - Coq ω-cpos, up to inverse limits for mixed-variance recursive domain equations.
  - Adequacy proofs for a typed and an untyped CBV language, using Pitts-style minimal invariance.
  - No compiler.
- **BentonHur10 [V-notes].** "we work with an operational, rather than a denotational, semantics for the high-level language". Not denotational.
- **HurDreyer11 [V-notes].** Operational on both sides.
- **Compared with ours:** BKV09 is the mechanized domain-theoretic adequacy precedent for λ-calculi, not for assembly. The other two are operational contrasts.

### 1.4 Interaction Trees (Xia et al., POPL 2020) and the ITree / Vellvm line

```bibtex
@article{XiaITrees20, author={Li-yao Xia and Yannick Zakowski and Paul He and Chung-Kil Hur and Gregory Malecha and Benjamin C. Pierce and Steve Zdancewic},
  title={Interaction Trees: Representing Recursive and Impure Programs in {Coq}}, journal={PACMPL}, volume={4}, number={POPL},
  pages={51:1--51:32}, year={2020}, doi={10.1145/3371119}}
@article{Vellvm21, author={Yannick Zakowski and Calvin Beck and Irene Yoon and Ilia Zaichuk and Vadim Zaliva and Steve Zdancewic},
  title={Modular, Compositional, and Executable Formal Semantics for {LLVM IR}}, journal={PACMPL}, volume={5}, number={ICFP}, year={2021}, doi={10.1145/3473572}}
@article{ChoiceTrees23, author={Nicolas Chappe and Paul He and Ludovic Henrio and Yannick Zakowski and Steve Zdancewic},
  title={Choice Trees: Representing Nondeterministic, Recursive, and Impure Programs in {Coq}}, journal={PACMPL}, volume={7}, number={POPL},
  pages={1770--1800}, year={2023}, doi={10.1145/3571254}}
```

The article number 51 in XiaITrees20 is [M]; the DOI is from Crossref.

- **XiaITrees20 [V].**
  - §5, "Case study: verified compilation of Imp to Asm".
  - §5.1 is "A Denotational Semantics for Imp" and §5.2 is "A Denotational Semantics for Asm". Asm is a CFG of basic blocks with registers and a heap.
  - "The denotational model enables us to state a termination-sensitive bisimulation and prove it purely [inductively]".
  - Semantics are monadic and coinductive (ITrees), with events interpreted into state monads.
- **Handles:** while loops, so divergence, yes. Closures and higher-order functions, no. One pass. Asm has no machine adequacy; the ITree is the reference semantics.
- **Vellvm21 [A].** ITree-based layered semantics for LLVM IR, with verified optimizations. No source-to-assembly compiler.
- **HELIX (Zaliva, Zakowski, … Zdancewic, arXiv 2604.18593, 2026) [A].** Verified compilation of numerical/control code to LLVM IR in Coq, using "layered monadic interpreters" (ITrees). First-order.
- **Kan & Ertel, arXiv 2605.04933 (2026) [A].** An ITree semantics of the RISC-V ISA in Rocq, with a bisimulation case study between LLVM IR (Vellvm) and RISC-V code. Not a higher-order compiler.
- **Compared with ours:** a mechanized "denotational" (monadic, coinductive) semantics for both source and assembly. But it is imperative and first-order, with no closures, no graph model, and no adequacy against a machine. Ours is set-theoretic rather than coinductive and handles higher-order code with closure conversion.

### 1.5 Cheng, Wu, Wang & Cao: denotation-based CompCert front end (TOPLAS 2026)

```bibtex
@article{ChengDenotCompCert26, author={Zhang Cheng and Jiyang Wu and Di Wang and Qinxiang Cao},
  title={Denotation-based Compositional Compiler Verification}, journal={ACM TOPLAS}, volume={48}, number={1},
  pages={5:1--5:65}, year={2026}, doi={10.1145/3797874}, note={arXiv:2404.17297}}
```

- **Metadata [A]** from the arXiv page: the journal ref and accepted-manuscript comment.
- **Content [V], from the arXiv v3 text.**
  - Each syntactic component denotes sets of behaviours (terminating, diverging, aborting, with event traces), and the operators "form a typed Kleene Algebra".
  - It is applied to "the front-end of CompCert" (Clight → Csharpminor → Cminor) and to toy WHILE / PCALL / GOTO / CFG languages. It is mechanized in Coq.
- **Handles:** divergence, yes, explicitly. Closures, no (first-order C). No graph model.
- **Compared with ours:** the most recent major venue paper doing multi-pass mechanized compiler verification with denotational semantics. It is relational / trace-set and first-order.
- **Also first-order, found in the final sweep [A, abstract via OpenAlex; Crossref metadata].** Bourke, Jeanmaire & Pouzet, "Functional Stream Semantics for a Synchronous Block-Diagram Compiler", LICS 2025, pp. 609–621, doi:10.1109/LICS65433.2025.00052 (the Vélus Lustre compiler): "Synchronous block-diagram languages have long been formalized as fixpoints of equations defining stream functions. We apply this approach to a compiler verified in an interactive theorem prover, allowing us to restate its end-to-end correctness theorem". A denotational (stream-function) source semantics for a mechanized compiler; first-order dataflow, no closures. Adds to the C1 list; does not affect C2–C9.

### 1.6 Compiler calculation: Hutton, Bahr and co-authors (Coq/Agda)

```bibtex
@article{BahrHutton15, author={Patrick Bahr and Graham Hutton}, title={Calculating Correct Compilers}, journal={JFP}, volume={25}, pages={e14}, year={2015}, doi={10.1017/S0956796815000180}}
@article{BahrHutton20, author={Patrick Bahr and Graham Hutton}, title={Calculating Correct Compilers {II}: Return of the Register Machines}, journal={JFP}, volume={30}, year={2020}, doi={10.1017/S0956796820000209}}
@article{PickardHutton21, author={Mitchell Pickard and Graham Hutton}, title={Calculating Dependently-Typed Compilers (Functional Pearl)}, journal={PACMPL}, volume={5}, number={ICFP}, year={2021}, doi={10.1145/3473587}}
@article{BahrHutton22, author={Patrick Bahr and Graham Hutton}, title={Monadic Compiler Calculation (Functional Pearl)}, journal={PACMPL}, volume={6}, number={ICFP}, pages={80--108}, year={2022}, doi={10.1145/3547624}}
@article{BahrHutton23, author={Patrick Bahr and Graham Hutton}, title={Calculating Compilers for Concurrency}, journal={PACMPL}, volume={7}, number={ICFP}, pages={740--767}, year={2023}, doi={10.1145/3607855}}
@inproceedings{GarbyHuttonBahr24, author={Zac Garby and Graham Hutton and Patrick Bahr}, title={Calculating Compilers Effectively (Functional Pearl)}, booktitle={Haskell Symposium}, pages={109--119}, year={2024}, doi={10.1145/3677999.3678283}}
```

- **BahrHutton15 [A].**
  - Coq formalisations of all calculations, per the repo README snippet. Some virtual machines are defined as relations.
  - Covers "various forms of lambda calculi" among other languages.
  - Only converging behaviour is considered, per the 2022 paper's abstract.
- **BahrHutton22 [V, paper PDF (PACMPL 6, ICFP, Article 93) and Zenodo README].**
  - Mechanization: "All the calculations have been mechanically checked in Agda" (§1, p. 93:2). The paper presents Haskell notation: "We use Haskell notation as our meta-language for accessibility, but assume that the language is total" (p. 93:2).
  - Divergence: the abstract says the earlier methodology "only considers converging behaviour", and the new one is "based on the use of the partiality monad to make divergence explicit, together with the use of strong bisimilarity" (p. 93:1). For the mixed induction/coinduction the paper says: "There are different frameworks for achieving this mixing of inductive and co-inductive reasoning methods, such as guarded recursion [Møgelberg and Veltri 2019] and sized types [Hughes et al. 1996]. To simplify the presentation, we have chosen a step-indexed approach" (§2.6, p. 93:11).
  - Pragmas: the paper text does not mention `TERMINATING` (no occurrence); that detail is from the artifact README: "the termination checker is disabled for `exec` (using the `TERMINATING` pragma) and termination is proved manually". The README also describes the evaluator as using sized types; the paper only names sized types as one option.
  - §3 source: "the untyped, call-by-value lambda calculus extended with integers and addition" (p. 93:11), with semantics `eval :: Expr → Env → Partial Value` and "the notion of a value includes both integer values and closures: data Value = Num Int | Clo Expr Env" (p. 93:12). A monadic definitional interpreter (environments and closures), not a graph model; the paper itself contrasts it only with big-step semantics: "the source semantics is now defined as a function into Partial Value, rather than as a big-step operational semantics" (§3.2, p. 93:13). It never calls it denotational.
  - §3 correctness: Theorem 3.1, `do v ← eval t e; exec c (VAL (conv v) : s, conv_E e)` ≃ `exec (comp t c) (s, conv_E e)` (strong bisimilarity, p. 93:13).
  - **No closure conversion [V, paper §3.3 and artifact `agda/Lambda.agda`]:** the VM keeps closures; the calculation defines "conv (Clo x e) = Clo′ (comp x RET) (conv_E e)" and "exec (ABS c′ c) (s, e) = exec c (VAL (Clo′ c′ e) : s, e)", "simply adding a new code constructor ABS that puts a closure onto the stack" (p. 93:16). Single calculated pass to a VM.
- **BahrHutton23 [A].** Codensity choice trees, a concurrent λ-calculus, Agda.
- **PickardHutton21 and GarbyHuttonBahr24 [A].** Dependently typed (total) and effect-handler variants, respectively.
- **Compared with ours:** a mechanized "semantics as a function" approach that includes divergence (since 2022). But each is a single calculated pass to a VM with closures, using a monadic interpreter rather than a set-theoretic denotation, and there is no closure conversion or assembly.

### 1.7 Danielsson, ICFP 2012, and Leroy & Grall 2009 (operational contrast)

```bibtex
@inproceedings{Danielsson12, author={Nils Anders Danielsson}, title={Operational Semantics Using the Partiality Monad},
  booktitle={ICFP}, year={2012}, doi={10.1145/2364527.2364546}}
@article{LeroyGrall09, author={Xavier Leroy and Herv{\'e} Grall}, title={Coinductive Big-Step Operational Semantics},
  journal={Information and Computation}, volume={207}, number={2}, pages={284--304}, year={2009}}
```

The Danielsson DOI is [M]. The Leroy–Grall metadata is [A].

- **Danielsson12 [V].**
  - Agda.
  - The definitional interpreter in the partiality monad is explicitly "not a denotational semantics".
  - Compiles an untyped λ-calculus to a VM taken from Leroy & Grall, and proves compiler correctness covering termination, divergence and crashes.
  - No closure conversion [V-notes].
- **LeroyGrall09 [A].** Coq. Coinductive big-step versus small-step semantics, with compiler correctness for a CBV λ-calculus to a VM.
- **Compared with ours:** both are useful as precedents for proving the same compiler with more than one semantic style, but only operational styles.

### 1.8 Other mechanized works with a "denotation" (total source, or the denotation is a shallow embedding)

```bibtex
@inproceedings{Oeuf18, author={Eric Mullen and Stuart Pernsteiner and James R. Wilcox and Zachary Tatlock and Dan Grossman},
  title={{\OE}uf: Minimizing the {Coq} Extraction {TCB}}, booktitle={CPP}, pages={172--185}, year={2018}, doi={10.1145/3167089}}
@inproceedings{Cogent16, author={Liam O'Connor and Zilin Chen and Christine Rizkallah and Sidney Amani and Japheth Lim and Toby Murray and Yutaka Nagashima and Thomas Sewell and Gerwin Klein},
  title={Refinement Through Restraint: Bringing Down the Cost of Verification}, booktitle={ICFP}, pages={89--102}, year={2016}, doi={10.1145/2951913.2951940}}
```

- **Œuf [V, author PDF from Tatlock's page, CPP '18 pagination].**
  - "a verified compiler from a subset of Gallina to assembly" (abstract), built on CompCert: "45 translation passes from our front end down to CompCert Cminor" (§4, p. 177), then CompCert.
  - **Only the source has a denotation**, a Coq function into Gallina terms (§3.3, "Denotational Semantics"), used for two things: translation validation of the untrusted reflection, and a theorem "that each step of the operational semantics (→) preserves the denotation (⟦·⟧): ∀ s s′, s → s′ ⇒ ⟦s⟧ = ⟦s′⟧" (§3.4, p. 176). The source is simply typed with eliminators instead of a fixpoint ("Eliminators were chosen instead of recursive functions due to their ease of denotation", p. 176), so it is total.
  - **Every pass is proved operationally:** "the Œuf compiler comes with a proof of simulation between an operational semantics for the Œuf input language and the operational semantics of Cminor", then "Œuf relies on CompCert's own simulation proof" (§2, p. 174); "the Œuf compiler includes simulation proofs for every translation pass" (§4.1, p. 177).
  - **No verified closure-conversion pass:** the source language already "has explicit closures" (closure creation names a top-level function plus environment expressions, §3.2, p. 176); lambda lifting is done in the untrusted reflection and checked by translation validation ("Performing lambda lifting during reflection allows us to avoid implementing a complex verified lambda-lifting pass in Coq", p. 177). Closures become memory by the "Heap Introduction" pass, proved by a simulation relation that "maps higher level values to their lower level memory representation" (§4.2, pp. 177–178).
- **Cogent [A].**
  - A certifying compiler for a total, linearly typed language.
  - The proof is that the generated C refines an Isabelle/HOL shallow embedding, i.e. a denotation into HOL functions.
  - No general recursion. Proofs are per program.
- **McKinna & Wright [A].** "A type-correct, stack-safe, provably correct expression compiler in Epigram". The JFP submission was dated 2006; the final publication is [M]. Arithmetic expressions only, total.
- **Pardo, Gunther, Pagano & Viera, "An Internalist Approach to Correct-by-Construction Compilers", PPDP 2018, article 17, 12 pp., doi:10.1145/3236950.3236965 [V, paper PDF; page numbers 17:n].**
  - Abstract: "a methodology to organize the construction of a correct compiler, taking advantage of the power of full dependently type systems. The basic idea consists in decorating the abstract syntax of languages with their semantics, allowing to express the correctness of the compiler at type level … a correct-by-construction compiler from an imperative language with conditional iteration to a stack based intermediate language … combined with the externalist approach, compiling from the intermediate language to an assembly-like low level code and separately proving its correctness."
  - **Proof assistant:** "We perform our development in Agda." (§1, p. 17:2).
  - **Languages and passes:** While (assignment, sequencing, `while`) → LCode, a stack code with `push`, `add`, `eq`, `load`, `store`, sequencing and a structured `loop[c1, c2]` (§3.5, p. 17:8) → Assm, "an idealized assembler for a machine that has a read-only memory for code" with relative jumps `jmp`/`jz` (§4, p. 17:10). First-order, no procedures, no closures.
  - **Semantics style:** clocked functions in Agda, which the paper calls denotational: "We use a finite approximation of the least fix-point whose accuracy is parameterized by a natural number (a clock), counting how many unfoldings of the loop will be done" and "The denotational semantics of a statement is a state transformer" with `DomSs = (clock : N) → (σ : State) → Maybe State` (§3, p. 17:7); for LCode, "As in the case of statements, we define denotational semantics with a clock to prevent infinite looping" (§3.6, p. 17:9). Assm has a small-step relation; "The transition semantics is the transitive closure of the single step relation" (p. 17:10).
  - **While → LCode** is internalist: the compiler's type `compStmts : ∀ {f} {st} → Stmts f → LCodes (compiledSem {st} f)` carries the semantics (§3.7, p. 17:9).
  - **LCode → Assm** is proved separately: "We prove the denotational semantics of LCode to be computational adequate with respect to the small-step semantics of Assm" (§4, p. 17:11). The statement is one direction: `realizes f is = ∀ {cl s s′ σ σ′} → f cl (s , σ) ≡ just (s′ , σ′) → is (0 , σ , unty* s) ⇝* (length is , σ′ , unty* s′)` ("if any proof that the function is defined for a given high-level configuration is mapped into traces", p. 17:11). End-to-end: `realizesWhile p tp is` (p. 17:11). Nothing is said about divergence (no clock yields `just` ⇒ no claim).
  - Future work: "We also project to target a low language closer to a realistic assembler language." (§5, p. 17:12).
  - **Effect on our claims:** another mechanized compiler proof whose source and intermediate semantics are (clocked) denotational, so one more reason not to claim C1. For C7: its "adequacy" relates the denotation of an LCode program to the machine run of the *compiled* Assm code (a compiler-correctness statement in the Benton–Hur shape, denotation on the high side only); Assm itself has no denotation, the statement is one direction (convergence), and the languages are first-order. It does not contradict C7 as phrased, but it is the nearest mechanized "denotational semantics adequate for an assembler" wording in print and should be cited when C7 is stated.
- **Compared with ours:** in all of these the denotation is the meta-language's own function space, and the source is total, except Pardo et al., whose While source is handled by clocked approximations; all are first-order or total.

### 1.9 Paper (non-mechanized) denotational compiler correctness: the historical line

```bibtex
@inproceedings{Morris73, author={F. Lockwood Morris}, title={Advice on Structuring Compilers and Proving Them Correct}, booktitle={POPL}, pages={144--152}, year={1973}, doi={10.1145/512927.512941}}
@article{TWW81, author={James W. Thatcher and Eric G. Wagner and Jesse B. Wright}, title={More on Advice on Structuring Compilers and Proving Them Correct},
  journal={Theoretical Computer Science}, volume={15}, pages={223--249}, year={1981}, doi={10.1016/0304-3975(81)90080-3}, note={Conference version ICALP 1979, LNCS 71:596--615}}
@book{Polak81, author={Wolfgang Polak}, title={Compiler Specification and Verification}, series={LNCS}, volume={124}, publisher={Springer}, year={1981}, doi={10.1007/3-540-10886-6}}
@article{Stoy81, author={Joseph E. Stoy}, title={The Congruence of Two Programming Language Definitions}, journal={TCS}, volume={13}, pages={151--174}, year={1981}, doi={10.1016/0304-3975(81)90037-2}}
@inproceedings{Clinger84, author={William Clinger}, title={The {Scheme} 311 Compiler: An Exercise in Denotational Semantics}, booktitle={LFP}, pages={356--364}, year={1984}, doi={10.1145/800055.802052}}
@inproceedings{Wand91, author={Mitchell Wand}, title={Correctness of Procedure Representations in Higher-Order Assembly Language}, booktitle={MFPS 1991}, series={LNCS}, volume={598}, pages={294--311}, year={1992}, doi={10.1007/3-540-55511-0_15}}
@inproceedings{WandOliva92, author={Mitchell Wand and Dino P. Oliva}, title={Proving the Correctness of Storage Representations}, booktitle={LFP}, pages={151--160}, year={1992}}
@inproceedings{Palsberg92, author={Jens Palsberg}, title={A Provably Correct Compiler Generator}, booktitle={ESOP}, series={LNCS}, pages={418--434}, year={1992}, doi={10.1007/3-540-55253-7_25}}
@article{VLISP95, author={Joshua D. Guttman and John D. Ramsdell and Mitchell Wand}, title={{VLISP}: A Verified Implementation of {Scheme}},
  journal={Lisp and Symbolic Computation}, volume={8}, number={1/2}, pages={5--32}, year={1995}, doi={10.1007/BF01128406}}
```

Venue details for TWW81's ICALP version and for Palsberg92 being ESOP '92 are [M]. The Crossref record only says LNCS 1992, pp. 418–434.

- **Morris73 and TWW81 [A metadata; content M].** Algebraic "commuting square" compiler correctness for simple languages, on paper.
- **Polak81 [V, the LNCS 124 book, chapters I–V, and the thesis it revises].** First read: W. Polak, *Theory of Compiler Specification and Verification*, PhD thesis, Stanford, 1980, report STAN-CS-80-802 (DTIC AD-A094604, scan on the Internet Archive as `DTIC_ADA094604`; pages read as images, thesis page numbers). The book (`related-denot/3-540-10886-6_{1..5}.pdf`, one PDF per chapter) was then read and every finding below holds for it; its text is nearly identical to the thesis (it still says "this thesis"), with book pages about one lower. **Book pages for the quotes:** "The Stanford verifier [SV79] is used to give a complete formal machine checked verification of the compiler." (p. 2); "we use denotational semantics for this purpose" (target, p. 16); §I.4.1 "What we prove" and "given that our compiler terminates then the above diagram commutes" (p. 17); "exit tmean(out) = dsem(in)" (p. 18); Milner–Weyhrauch and Diffie (p. 24), Cohn (p. 25); "Although the development of a suitable logical basis for our compiler verification is done manually all actual program proofs are completely machine checked." (p. 26); "Procedures and functions may not be passed as parameters." (§III.1, p. 53); target continuations "G = D → S → M → A" (§III.6.2, p. 81); §IV.5.3.5 "Existence of recursive predicates" (pp. 126–127), with "If l increases ϑ_S becomes smaller" and the appeal to Reynolds's criteria on p. 127. The book's chapter IV restates the theorem without the diagram: "We prove that whenever comp x terminates producing code y, then tmean y = smean x. Note, that this correctness statement cannot be expressed by a commuting diagram." (§IV.1.1.1). It also says of code-generation proofs in Milne–Strachey: "Similar proofs are checked mechanically with LCF by A. Cohn [Co79b]." (p. 114). Thesis page numbers follow.
  - **Denotational, yes.** Source and target are both given Scott–Strachey continuation semantics: "the source language by specifying a function smean mapping character strings into their meaning" (§I.3.4, p. 17); for the target "we use denotational semantics for this purpose" (§I.3.3, p. 17); §III.2.2 is "Denotational semantics" and §III.2.2.3 "Denotational definition of a machine language" ("Continuations in the target language are mappings of the form D → S → M → A", p. 62). The logic is Scott's LCF (§II.2, "Scott's logic of computable functions").
  - **Correctness statement:** a commuting square with smean, tmean and the identity, read as partial correctness: "the correct statement is 'given that our compiler terminates then the above diagram commutes'" (§I.4.1, p. 18); for the code generator, "exit tmean(out) = dsem(in)" (p. 19).
  - **Machine-checked, in part.** Abstract (p. iii): "The Stanford verifier is used to give a complete formal machine checked verification of the compiler." But §I.5.2 (p. 27): "Although the development of a suitable logical basis for our compiler verification is done manually all actual program proofs are completely machine checked." The compiler is a Pascal Plus program verified with the Stanford Pascal Verifier against its specifications; the theory those specifications rest on (lemmas about the semantics) was developed by hand. The relations between source and target domains (§IV.5.3.4, ϑ predicates) are recursive and non-monotone; their existence is not proved but assumed by appeal to Reynolds 1974: "To repeat the theory of 'inclusive' predicate is beyond the scope of this thesis. However, Reynolds [Re74] presents a set of easy to check criteria that ensure existence of fixed points. It can be seen that our definitions satisfy his criteria; thus we subsequently assume that the above predicates are well defined." (§IV.5.3.5, p. 136).
  - **Languages:** LS, a Pascal subset with recursive procedures and functions, jumps, arrays, records and pointers (abstract, p. iii); **first-order**: "Procedures and functions may not be passed as parameters" (§III.1.2, p. 57). Target LT: "assumes a stack machine including a display mechanism [RR64, Or73] to handle procedure and function calls" (p. 2), a hypothetical machine (§III.7). No closures, no closure conversion; the compiler is scanner, parser, static semantics and a single code generator (§I.4.1, p. 19).
  - **No closure conversion, and why [V, book §III.2, pp. 64–66, read 2026-10-16].** Nested procedures access non-local variables through a *display*: "If a procedure p with lexical level n is called, then at least one incarnation of all procedures with smaller lexical level (< n) which contain the declaration of p has to exist. If q is such a procedure with lexical level m, m < n, then the most recent incarnation of q is said to be the static predecessor of p of level m", and its frame is used to convert a non-local variable's relative address into an absolute one. Footnote 3 on that sentence: "This is not true for languages that allow for procedural parameters." So the ban on procedure parameters (§III.1, p. 53, motivated there by run-time type checking) is what lets every non-local variable live in a stack frame that is still active, found through the display; no closure (code plus captured environment) is ever built, and no heap allocation of environments is needed.
  - **Effect on our claims:** it is an early (1980) machine-checked compiler proof stated with denotational semantics, so it is another reason not to claim C1. It does not touch C2–C9: first-order source, no recursive types, no closure conversion, a hypothetical stack machine whose meaning is its denotation (no adequacy), and the semantic theory itself is not mechanized.
- **Earlier mechanized work cited by Polak [V that Polak says this; primary texts not read].** §I.5.1 (pp. 25–26): "The same proof method is used by Milner and Weyhrauch [MW72, WM72] in 1972 to verify a compiler for an algolic language. But they introduce yet another innovation: semantics and proof are described in Scott's logic of computable functions"; "Avra Cohn [Co79a, Co79b] proves the correctness of several components of a compiling algorithm using the Edinburgh implementation of LCF". Also "A machine checked proof of the McCarthy/Painter compiler has been done by W. Diffie but has not been published." (p. 25). Milner & Weyhrauch, "Proving compiler correctness in a mechanized logic", Machine Intelligence 7, 1972 [M for the venue details]. These are first-order (algolic) and predate Polak; again only relevant to C1. **Checked 2026-10-16 (secondary sources only; the primary paper is not online):** Gordon, "From LCF to HOL: a short history" (§2) says Weyhrauch "worked on the proof of correctness of a compiling algorithm for a simple imperative language to a stack-based target language" in Stanford LCF; Leroy, "A formally verified compiler back-end" (JAR 2009, §related work) says Milner and Weyhrauch "were arguably the first to mechanically verify semantic preservation for a compilation algorithm (the translation of arithmetic expressions to stack machine code), using the Stanford LCF prover". So first-order, no closures, no closure conversion. The two descriptions differ (simple imperative language versus arithmetic expressions); the companion paper Weyhrauch & Milner, "Program semantics and correctness in a mechanized logic", Proc. USA–Japan Computer Conference 1972, pp. 384–392, may be the one with the imperative language. Page range of the Machine Intelligence 7 paper: 51–70 (Gordon, Young) or 51–72 (Leroy).
- **Martin & Toal, "Case Studies in Compiler Correctness Using HOL", International Workshop on the HOL Theorem Proving System and Its Applications, 1991, pp. 242–252, doi:10.1109/HOL.1991.596291 [Crossref metadata; abstract A via OpenAlex].** "In the first case study, the source and target language semantics are direct denotational, and the compiler correctness proof is done by structural induction supplemented by computation induction where necessary. In the second case study, the source and target languages are given a structural operational semantics". Source "a sample imperative sequential language", target "abstract, stack-based, and executes tree-structured code". The abstract describes one source language and one target machine for both studies; whether it is literally the same compiler proved twice is unverified (body not read). If it is, it is an early instance of **one compiler proved both denotationally and operationally in a proof assistant** (relevant to C9): a toy imperative language, one pass, first-order, so C9's "multi-pass" and "three operational styles" still separate ours.
- **Stoy81 [V, `related-denot/stoy-1981.pdf`, OCR text layer of a scan; quotes have OCR misspellings silently corrected, words lost in the OCR are not filled in].** Not a compiler: a congruence proof between a direct denotational semantics of a small language PL and "an interpreter, along lines similar to the use of VDL" (p. 151), through an intermediate continuation semantics. Paper proof; it hopes that "increased use of mechanical aids, such as those developed by Milner and others [10], will relieve this situation" (p. 169). Details in Part III B4. Does not affect C1–C10 beyond the C6 background.
- **Clinger84 [V, `related-denot/clinger-1984.pdf`; details in `vlisp-clinger-wand.md` §2].** "This paper describes and proves the correctness of a simple compiler algorithm for Scheme" (p. 356), against a simplified standard continuation semantics, into code "for a hypothetical and rather abstract Scheme machine" (p. 357) whose instructions are given "a continuation semantics for each instruction" (p. 359), in the same domains as the source. The target has a closure-building `lambda` instruction (Figure 4, p. 360), so there is no closure conversion. The theorem equates the meaning of the compiled code with "the standard meaning of the expression" (p. 360); the proof is a paper sketch "by induction on E and E*" (p. 360). Not mechanized; no machine, so no adequacy. Its own claim: "the first in that line to prove the correctness of a usable compiler for a real programming language" (p. 363).
- **Wand91 [A, plus V-notes].** Closure and procedure representations are handled inside a single λ-theory by a conservative-extension theorem. On paper. **Classification (author, 2026-10-15): not denotational.** Meanings are λ-terms up to convertibility, which is not extensional, and there is no model (only the sketched conservativity proof uses the open term model). Describe it as a compositional translation into an equational λ-theory (the Wand–Clinger single-theory approach). See `vlisp-clinger-wand.md` §3. Wand's index page [V] describes the paper's own summary as "proves a compiler from a tiny language into HOAL correct".
- **WandOliva92 [V-notes].** "relations on terms (not their denotations)". The Wand–Clinger "single model" approach models the target machine in the same domains as the source.
- **VLISP95 [A, plus Benton–Hur's characterisation V].**
  - Scheme to byte code, based on the Clinger–Rees denotational semantics. Untyped, with recursion and closures.
  - "the proofs were not mechanized" (Benton & Hur 2009).
  - **The faithfulness report [V].** Farmer, Guttman, Monk, Ramsdell & Swarup, "Faithfulness of the VLISP Operational Semantics", MITRE M92B093, September 1992, 37 pp. Found as `faithfulness.dvi.Z` (TeX output 1993-03-10) in the Indiana Scheme Repository, `ftp.cs.indiana.edu/pub/scheme-repository/doc/pubs/vlisp/`, via the Wayback Machine (capture 2006-09-03); the 1993 announcement on the rrrs-authors list gives the same title and number. Abstract (p. iii): "This report provides a detailed proof that the operational semantics for the highest-level interpreter (virtual machine) is faithful to the denotational semantics used in the byte-code compiler proof."
    - Level: "The two semantics are compared at the Tabular Byte Code (tbc) level, since tbc is assigned both kinds of semantics" (§1, p. 1). Byte code with primitive closures (`⟨closure t u l⟩` values, p. 1).
    - Statement, one direction only: "The operational semantics for tbc is faithful if, for all tbc templates t and all initial states Σ for t, D[[Σ]] = O[[Σ]] whenever O[[Σ]] is defined." (§4, p. 4; Theorem 5.5, p. 6). So if the machine halts with an answer, the denotation is that answer; nothing is said when the denotation is an answer and the machine does not halt (the converse that GSS p. 6 says is not established).
    - Method: give every machine state a denotation (new semantic functions D_v, D_a, D_u, D_k, D_s, §2) and show each machine rule preserves it: "Lemma 5.3 If Σ and Σ′ are normal abc states such that O′[[Σ]] is defined and Σ′ = R(Σ) for some special rule R, then D[[Σ]] = D[[Σ′]]", a 34-case proof (§6, pp. 7–34). Paper proof.
    - This is the nearest **paper** precedent for target-side adequacy: soundness of a byte-code machine against a denotation, on paper, one direction, for a VM with closures.
- **Palsberg92 [A metadata only].** Compiler generation from action semantics. Paper proof.
- **Compared with ours:** these are the conceptual ancestors (denotational compiler correctness, closure representations, and a denotation-to-machine faithfulness proof). Polak's program proofs are machine-checked (the semantic theory is not), and the LCF work of Milner–Weyhrauch and Cohn is mechanized (per Polak); all of these are first-order. The higher-order ones (Clinger, Wand, VLISP) are on paper, and Clinger's target, like VLISP's byte code, has primitive closures [V]. None uses a graph model.

### 1.10 Operational contrast (one line each)

All of these are [A] or [V-notes]; the details are in Part II.

- **CompCert, CompCertO, CompCertTSO:** operational simulations.
- **CakeML:** functional big-step semantics with clocks.
- **CertiCoq (Paraskevopoulou & Appel, ICFP 2019; Paraskevopoulou, Li & Appel, ICFP 2021):** step-indexed logical relations, untyped closure conversion.
- **Pilsner (ICFP 2015):** parametric inter-language simulations.
- **Chlipala, POPL 2010:** big-step semantics, terminating programs only.
- **Wang & Nadathur, ESOP 2016:** Abella.
- **Pyrosome (OOPSLA 2025):** equational theories.
- **Minamide, Morrisett & Harper (POPL 1996), and Ahmed & Blume (ICFP 2008):** operational, typed closure conversion.
- **Brack (Lasnier, Yallop & Myreen, CPP 2026) [A, abstract via OpenAlex]:** Scheme (with first-class continuations and functions) to CakeML in HOL4, via a CPS transformation "that naturally arises from Scheme's small-step semantics". Operational.
- **Siek, "Verified Nanopasses for Compiling Conditionals", OlivierFest 2025 (ICFP/SPLASH 2025) [V, the paper source `paper/paper.tex`, `abstract.md` and the Agda files in the public repository github.com/jsiek/correct_compilers; the venue is from the researchr programme page, A].** For a third-person citation:
  - Abstract: "We present a proof of correctness in Agda for four nanopasses that translate a source language with let binding, integer arithmetic, conditional expressions and Booleans into an x86-flavored register transfer language. The most interesting of these four nanopasses is a translation of conditional expressions into goto-style control flow that uses the continuation-oriented approach of Olivier Danvy's one-pass transformation into monadic normal form (2003)."
  - Passes (README): rco (LIf → LMonIf), lift-locals (→ ILIf), explicate (→ CIf, a C-like language with goto), select-inst (→ X86If, "X86 assembly but with variables"); the passes come from *Essentials of Compilation*. Closure conversion is mentioned but "not discussed here".
  - **Semantics: operational, a mixture of definitional interpreters and big-step relations, as the author said.** The source and the monadic-normal-form language have interpreters: "The semantics of expressions is given by the interp-exp function", `interp-exp : Exp → Env Value → Reader Value`, with `Maybe` for partiality. For the imperative IL "we switch to representing the semantics as a relation, that is, a big-step semantics" (`interp-imp : Imp-Prog → Inputs → Value → Set`); the C-like language and X86 also get big-step relations ("We choose a big-step semantics for the C-like language because the semantics is no longer structurally recursive and furthermore, programs are no longer guaranteed to terminate", with a footnote that programs in the image of explicate do terminate). The paper's CCS concept is "Theory of computation~Operational semantics".
  - Theorem (`LIf2Correct.agda`): `compile-correct : (e : Exp) (s : Inputs) (v : Value) → interp-LIf e s ≡ just v → interp-x86-var (compile e) s v`, i.e. forward preservation of the final value. The source has no functions or loops, so every program terminates.
  - Relation to ours: same author and the same textbook pipeline for the back-end passes (rco, explicate control, select instructions), but first-order, total, no closures, and operational; a precursor for the back end, not for the graph-model method.

Every mechanized closure-conversion proof for an untyped, Turing-complete language found so far is operational.

---

## (2) Mechanized graph, filter and intersection-type models of the λ-calculus

```bibtex
@misc{Siek17, author={Jeremy G. Siek}, title={Revisiting Elementary Denotational Semantics}, year={2017}, eprint={1707.03762}, archivePrefix={arXiv}}
@article{SiekAFP, author={Jeremy G. Siek}, title={Declarative Semantics for Functional Languages}, journal={Archive of Formal Proofs}, year={2017}, note={\url{https://isa-afp.org/entries/Decl_Sem_Fun_PL.html}}}
@misc{PLFA, author={Philip Wadler and Wen Kokke and Jeremy G. Siek}, title={Programming Language Foundations in {Agda}}, howpublished={\url{https://plfa.github.io/}}, note={Part 3: Denotational, Compositional, Soundness, Adequacy, ContextualEquivalence}}
@misc{Siek19, author={Jeremy G. Siek}, title={Transitivity of Subtyping for Intersection Types}, year={2019}, eprint={1906.09709}, archivePrefix={arXiv}}
@misc{MossesCockxReus26, author={Peter D. Mosses and Jesper Cockx and Bernhard Reus}, title={Mechanising Denotational Semantics in {Agda}}, year={2026}, eprint={2610.14898}, archivePrefix={arXiv}, note={to appear, MFPS 2026}}
```

The AFP year for SiekAFP is [M]. The outline PDF I saw is dated 2025, which is just the regenerated build.

- **Siek17 (arXiv, v4 21 Oct 2017) [V abstract, from the arXiv API record of v4; V-notes for §5–6].**
  - **Language [V, PDF read 2026-10-16].** The untyped λ-calculus (with integers and arithmetic for the optimizer, §6): "The use of subset … is critically important, as it enables self application and thereby general recursion via the Y combinator" (§2), and a non-terminating call gets the meaning ∅. So the source has general recursion and divergence; Siek 2017 misses K3 and K4, not K2. §7 also treats System F with `fix`.
  - A graph model for CBV λ: "we create a new model that represents functions literally as finite graphs".
  - Exact wording of the priority sentence: "Regarding mechanization, we give the first machine-checked proof of soundness and completeness of an elementary model with respect to an operational semantics." The next sentence: "Regarding compiler correctness, we define a polyvariant inliner for the call-by-value λ-calculus and prove that its output is contextually equivalent to its input." (arXiv comment on v4: "25 pages, revision of POPL 2018 submission, now under submission to ESOP 2018".)
  - A polyvariant **inliner** is proved correct by equality of denotations plus soundness for contextual equivalence. It is mechanized in Isabelle.
  - This is an optimization **within one language**.
- **SiekAFP [A, AFP outline].**
  - Four views of the semantics.
  - Case studies: an inlining optimization, semantic type soundness for a polymorphic λ-calculus with general recursion, and mutable references.
  - "We have not yet investigated whether it is fully abstract."
- **PLFA, Part 3 (Siek's chapters) [V-notes].**
  - An Agda filter / graph-style model (`⊥`, `_↦_`, `_⊔_`) for the untyped CBN λ-calculus.
  - Compositionality, soundness, adequacy (via the 𝕍/𝔼 relation, by recursion on Value), and contextual equivalence.
  - No compiler.
- **Siek19 [A].** BCD subtyping without a transitivity rule. Motivated by "filter models for compiler verification", which is a stated programme, not a result.
- **MossesCockxReus26 [V, arXiv v1 full text; to appear in MFPS 2026 per the arXiv comment].** Scott–Strachey denotational definitions embedded in Agda with postulated domain constructors: "We have developed a collection of Agda modules with postulated types for commonly used domain constructors and their associated operations", illustrated by "a model of the untyped λ-calculus, Plotkin's denotational semantics of PCF, and a semantics of a sublanguage of Scheme" (abstract). It also says "Some of the postulated properties of our definitions are inconsistent with a classical set-theoretic interpretation of Agda." **No compiler:** the full text contains no compiler; the only occurrence of "compil" is the title of Mosses's 1975 thesis in the references. Not `--safe`-style (postulates).
- **Mosses 2025 [V, the artifact's repository github.com/pdmosses/scheme25-agda and its LaTeX listing; Crossref].** Paper: Mosses, "Checking a Denotational Semantics of Scheme in Agda", Scheme Workshop 2025 (26th ACM SIGPLAN International Workshop on Scheme and Functional Programming), doi:10.1145/3759537.3762694; artifact doi:10.1145/3747410. The repository "gives a shallow embedding into Agda of the denotational semantics from the 5th Revised Report (R5RS)"; its modules are Abstract-Syntax, Domain-Equations, Semantic-Functions, Auxiliary-Functions and Notation. **No compiler.** The paper body itself was not obtained (ACM 403), only its abstract opening via OpenAlex and the artifact.
- **Domain-theoretic, not graph models:**
  - de Jong & Escardó, Scott's D∞ in Agda/TypeTopology [V-notes abstract].
  - BKV09 in Coq [V-notes].
  - Garlene, guarded recursion in Lean, arXiv 2609.24345 [A]: it re-proves adequacy for a λ-calculus with fixpoints and says the results are not new.
- **Intersection-type mechanizations without models used for compilation:**
  - Laurent's Coq proof of BCD transitivity [A, via Siek19].
  - Larchey-Wendling's constructive λ-calculus in Coq, with intersection systems D and DΩ [A].
- **Not found:** any Coq, Lean or Agda development using a graph or filter model as the semantics of a compiler between *different* languages, apart from this project. The final sweep (see "Final searches" below) found nothing new: the only hits for "filter model" with "compiler" are Siek17 and Siek19, and every web hit for graph-model closure conversion is this project's own public GitHub issues and pull requests.
- **Verdict for (2):** the only mechanized uses of graph or filter models for program transformations that I found are Siek's own: the Isabelle inliner (2017) and the AFP entry. Both are same-language.

---

## (3) Mechanized adequacy of a denotational semantics for a low-level / assembly target

- **Chlipala07 [V].** Asm gets a trace denotation, but there is no separate machine semantics and no adequacy theorem. The denotation is the definition.
- **XiaITrees20 [V].** Asm gets an ITree denotation. The ITrees are executable by extraction, but there is no adequacy theorem against a separately defined machine. The paper contrasts itself "with non-executable models based on small-step operational semantics".
- **Kan & Ertel 2026 and Vellvm [A].** ITree semantics for RISC-V and LLVM IR. Validated by test suites; no adequacy against an independent machine was seen.
- **Benton & Hur 2009 [V].** Relates a *source* denotation to machine behaviour. Lemmas 5 and 6 are named "Adequacy for bottom" and "Ground termination adequacy". The low-level side has no denotation, so this is the inverse of our setting.
- **RockSalt / bigrammar decoder DSL (Coq) [A].** Denotational and operational semantics of an x86 *decoder* DSL, with adequacy between them. Not program execution.
- **VLISP [V, M92B093; see Part I §1.9].** Faithfulness of the tbc byte-code machine to its denotational semantics: one direction (machine answer ⇒ same denotation), on paper, byte code with primitive closures.
- **Tune & Kavvos, "Bimodels and Biorthogonality for Abstract Machines", PACMPL 10 (ICFP), Article 288, 2026, doi:10.1145/3828686 [V, paper PDF; artifact doi:10.5281/zenodo.20507720].**
  - Abstract (p. 288:1): "We develop a compositional semantics for abstract machines, focusing on CK/CEK machines for call-by-push-value. … Each has a syntactic instance, built from the machine itself, and a set-theoretic instance that serves as a denotational semantics. … Different instantiations yield canonicity, adequacy, operational extensionality, internal full abstraction, and a first-order simulation theorem relating the CK and CEK machines. All results are mechanized in Agda."
  - Language: CBPV, typed and total: "Even though we do not treat either recursion or effects in this work" (p. 288:2).
  - **Mechanized adequacy of a denotational semantics against an abstract machine, yes.** Theorem 5.3 (p. 288:14): "Let σ be a first-order value type, ⊢c M : Fσ, and ⊢v V : σ. If ⟦M⟧ = ⟦return V⟧ in the set-theoretic bimodel, then ⟨M | ⊙⟩ ⇝* ⟨return V | ⊙⟩." For the CEK machine, "The set-theoretic environment bimodel gives a denotational semantics for the CEK machine" (§7.2, p. 288:22), and Theorem 8.3 (p. 288:25) is the same statement for CEK closures up to normal forms. One direction (denotation returns a first-order value ⇒ machine returns it); no divergence (the language is total).
  - Not assembly: the machines run CBPV terms with stacks (CK) or closures and environments (CEK); there is no compiler (the CK–CEK simulation relates two machines for the same terms). Related work: "Neither Benton and Hur [2009] nor Rodriguez et al. [2016] give the stacks of their machines a denotational interpretation" (p. 288:27).
  - **Effect on C7:** C7 cannot be stated as "first mechanized adequacy of a denotational semantics against an abstract machine"; Tune & Kavvos (Agda, 2026) did that for CK/CEK machines of a total CBPV. C7 survives only with "assembly-level language" (and, as a distinguishing point, recursion/divergence and both directions if our theorem has them).
- **Pardo, Gunther, Pagano & Viera, PPDP 2018 [V; see Part I §1.8].** "We prove the denotational semantics of LCode to be computational adequate with respect to the small-step semantics of Assm" (p. 17:11), mechanized in Agda. The denotation is of the structured stack IL LCode; the machine runs the *compiled* Assm code, so this is a one-direction compiler-correctness statement (denotation defined with some clock ⇒ the assembler run reaches the final configuration), not adequacy of a denotation *of* the assembly language. First-order, no divergence claim.
- **Verdict for (3):** I found no mechanized adequacy proof of a denotational semantics (of any kind, let alone a graph model) *of an assembly-level language* against a machine for that same language. Mechanized adequacy of a set-theoretic semantics against CK/CEK machines exists (Tune & Kavvos 2026, total CBPV, one direction), and Pardo et al. 2018 mechanize a one-direction "adequacy" of a stack-IL denotation against the small-step run of the compiled assembler code. The nearest assembly-level precedents remain VLISP (paper, byte code, one direction) and the Coq decoder DSL (not execution).

---

## (4) Game semantics (contrast, one line each)

- **Ghica, "Geometry of Synthesis", POPL 2007, doi:10.1145/1190216.1190269 [A, abstract via OpenAlex].** Hardware synthesis from an SCI-typed higher-order language using "a semantic model inspired by game semantics and the geometry of interaction … A soundness result is given, which is also a correctness result for the compilation technique." A semantics-directed compiler to circuits with a paper soundness proof; no mechanization seen (GoS IV, ICFP 2011, doi:10.1145/2034773.2034805 [A], extends it to affine recursion and benchmarks it; no mechanization mentioned). Not a counterexample: target is hardware, the model is game/GoI, not mechanized.
- **CompCertO (Koenig & Shao, PLDI 2021) [V, author PDF].** Keywords include "Game Semantics"; §2.1 introduces game semantics as "a form of denotational semantics which incorporates some operational aspects", but semantics stay transition systems (§2.2: "Under the traditional CompCert semantics, programs are interpreted as transition systems which define strategies for the game E → W"; CompCertO generalizes the interfaces of these transition systems), and the correctness proofs are CompCert-style simulations under "simulation conventions". Operational, game-inspired interfaces. Contrast only.

---

## Synthesis: how the verdicts changed (the table of claims and verdicts is §1 at the top)


No verdict changed in the gap-closing pass. C1 gains older counterexamples (Polak, the LCF work, Martin–Toal) and stays "do not claim"; C6, C7 and C9 gain notes but keep their safe phrasings; C2, C3, C4, C5, C8 and C10 are unaffected.

Third pass (PDFs in `related-denot/`): no verdict changed. C1 gains Pardo et al. 2018 and keeps "do not claim". C6 loses its Filinski and Stoy caveats (neither indexes by finite elements; Stoy's asymmetric predicates relate a denotation to an interpreter) and keeps its phrasing. C7 keeps "supported", but only in the assembly-level form: its broad parenthetical ("any denotational semantics … against an abstract machine") is contradicted by Tune & Kavvos 2026, and the safe phrasing now names "a machine for that language" so that Pardo et al.'s cross-language statement is not a counterexample. C3/C4 are unaffected: Clinger's and Bahr–Hutton's targets keep primitive closures [V].

### Final searches (2026-10-15)

- **Run:** OpenAlex title/abstract search ("graph model" + "compiler correctness"; "filter model" + "compiler correctness"; "filter model" + compiler; "denotational semantics" + "closure conversion"; "adequacy" + "assembly language" + "denotational semantics"; "denotational" + "compiler correctness" + mechanized; "logical relation" + "two denotational semantics"; "denotational semantics" + compiler + Agda); the arXiv API abstract search (graph model/filter model/intersection types with compiler; denotational with closure conversion, compiler correctness, verified compiler, or a proof assistant name; adequacy with assembly or x86; "elementary model"); and web searches for the same combinations.
- **Blocked:** Google Scholar (HTTP 429 on every query), Semantic Scholar API (429, retried), DBLP (bot check on both dblp.org and dblp.uni-trier.de), ACM DL (403). No Scholar or DBLP sweep was completed.
- **Hits that touch a claim:** Martin & Toal 1991 and Bourke et al. 2025 (C1; C9 note), Tune & Kavvos 2026 (C7: rules out the broad "abstract machine" form; see §3), Rodríguez–Pagano–Fridlender 2016 and Brack 2026 (contrast). Nothing found affects C2, C3 or C6. The only graph-model closure-conversion hits are this project's own public GitHub issues and pull requests (a double-blind concern, not a novelty one).

### Remaining unverified gaps (check before submission)

Closed in the third pass: Polak's book (now read; book page numbers are given in Part I §1.9), Pardo et al. 2018 (paper read), Bahr–Hutton 2022 §3 (paper read), Tune & Kavvos 2026 (paper read), Clinger 1984 (paper read).

1. **Milner–Weyhrauch 1972, Cohn 1979, Martin–Toal 1991:** known only through Polak's description or an abstract. Read them before describing them in more than one line, in particular whether Martin–Toal prove the same compiler twice.
2. **Not checked: "Kavvos"** in the earlier sense (no compiler-correctness paper found; dropped). The 2026 ICFP paper above is the only new Kavvos hit.
3. **Not checked: Hutton & Wright, "Compiling exceptions correctly", and other paper-only calculational works.** Mention generically.
4. **Google Scholar and DBLP full-text sweeps** could not be run (blocked). OpenAlex and arXiv found nothing affecting C2/C3/C6/C7, but they search titles and abstracts only.
5. **Stoy 1981 and Clinger 1984 quotes** come from OCR text layers of scans; check them against the printed page before quoting in the paper.


---

# Part II. Closure conversion, denotational semantics, and mechanized proofs

(The survey of 2026-10-09 for the delay-pass proof; formerly `related-work-closure-conversion.md`. Several works, such as Chlipala 2007, Danielsson 2012 and Benton–Hur 2009, are also covered in Part I, which was checked against more primary sources; where they differ, trust Part I.)

Literature survey compiled 2026-10-09 for the delay-pass proof
(see [issue #1](https://github.com/jsiek/denotational_semantics/issues/1)
and `blog/stuck.md`).

Each entry says how closely it was checked:

- **[read]**: the relevant part of the paper or page was read directly.
- **[abstract]**: checked only from the abstract, the publisher page, or search snippets.
- **[known]**: a standard reference cited from memory and not re-checked in this search. Verify before citing.

## Bottom line

1. **No direct precedent found.** Nothing in the search proves closure conversion correct for an *untyped* language against a *denotational* semantics on both sides. Nothing uses graph or filter models for this either.
2. **No precedent for the proposed relation.** Nothing found defines a logical relation indexed by *finite sets of graph-model observations from one side*, which is the proposal in issue #1.
   - The nearest relatives are Abramsky's "compact elements as formulas" view, Pitts's relational properties of domains, and the older inclusive-predicate method (Milne–Strachey, Reynolds, Mulmuley).
   - None of these is stated in this form, so the idea may be new. A closer read of the domain-theory and intersection-type literature is needed before claiming that.
3. **The closest denotational precedent is Chlipala (PLDI 2007), but its source is STLC, which is typed and total.** It notes that its target domains "allow more behavior" than the source, which is the same phenomenon as the junk entries here. Typing sidesteps the problem, and with no recursion there are no recursive domains. Chlipala's untyped follow-up (POPL 2010) includes closure conversion, but it is operational and covers terminating programs only.
4. **Untyped mechanized proofs mostly avoid Pitts.** Mechanized proofs of closure conversion for untyped or dynamically typed languages are almost all *operational* and *step-indexed*: CertiCoq, CakeML, Pilsner. One Coq paper (2208.14260) reports that Pitts-style untyped relations fail Coq's strict-positivity check. Agda has the same check.
5. **A third way to discharge `▷`.** Guarded domain theory and partiality-monad semantics give denotations that contain steps, so `▷` can be discharged (Møgelberg–Paviotti; Danielsson). This is a third option beside the finite-observation relation and Pitts, and it is closest to the `step-indexed/` experiments in this repo.

## Comparison table

One row per compiler or transformation paper, starting with this project. Purely theoretical works (Pitts, Reynolds, Abramsky, guarded domain theory) have no compiler and are not included.

**Reading the cells**
- "?" means the cell was not confirmed from what was read; check the paper.
- **TC** means the source language is Turing complete.
- **CC** means closure conversion.
- **LR** means logical relation.

| Work | Source language | TC | Semantics | CC | Other passes | Proof technique | Mechanized | Divergence |
|---|---|---|---|---|---|---|---|---|
| **This project: delay pass (Clos3 → Clos4)** | **Untyped ISWIM-like λ with tuples and sums** | **Yes** | **Denotational on both sides (graph models)** | **Yes** (delay is the core step) | Earlier stages: enclose, optimize, concretize | Proposed: one-sided relations indexed by finite observations | **Agda** (in progress) | Yes (one side denotes ∅ exactly when the other does) |
| Chlipala, PLDI 2007 | STLC | No (total) | Denotational into Coq types; coinductive traces from `Alloc` on | Yes | CPS, allocation, flattening, codegen | Type-indexed LR | Coq | Not in source (total) |
| Chlipala, POPL 2010 | Untyped Mini-ML with references and exceptions | Yes | Big-step operational (PHOAS, closure heap) | Yes | CPS, CSE, codegen | Simulation over derivations; code related syntactically | Coq | No (terminating programs only) |
| Danielsson, ICFP 2012 | Untyped λ with constants | Yes | Closure-based interpreter in the partiality monad ("not denotational"); functional small-step VM | **No** (λ compiles to a VM closure) | Compile to stack VM | Structural value map `comp_v`; weak bisimilarity | Agda | Yes, plus crashes |
| Benton & Hur, ICFP 2009 | Simply typed λ with recursion | Yes | Source: domain-theoretic denotational. Target: SECD-style operational | No | Compile to SECD-style machine | Biorthogonal, step-indexed LR | Coq | Yes |
| Nielsen, BRICS 2000 | Typed functional language | ? | Denotational | No (defunctionalization) | — | LR | No (paper) | Terminating programs only |
| Paraskevopoulou & Appel, ICFP 2019 (CertiCoq) | Untyped CPS λ (an IL; the source is Gallina) | Yes (IL) | Operational, with profiling (time/space) | Yes (flat closures) | Part of CertiCoq | Step-indexed LR | Coq | ? |
| Paraskevopoulou, Li, Appel, ICFP 2021 (CertiCoq) | Untyped λ ILs | Yes (IL) | Operational | Yes | Uncurrying, inlining, shrink reductions, … | Step-indexed LR, composed across passes | Coq | Yes |
| CakeML backend (Owens et al. 2017; Tan et al. 2019) | Typed ML source; CC is on the untyped IL ClosLang | Yes | Functional big-step with clocks | Yes (`clos_to_bvl`) | Many backend passes | Simulation | HOL4 | Yes (clocks) |
| Pilsner, ICFP 2015 | ML-like higher-order imperative language | Yes | Operational | ? | Multi-pass, through a CPS IL | Parametric inter-language simulations | Coq | ? |
| Wang & Nadathur, ESOP 2016 | Typed functional language | ? | Operational | Yes (typed CC) | CPS, code hoisting | Step-indexed LR | Abella (λProlog) | ? |
| Savary Bélanger, Monnier, Pientka, CPP 2013 / JFR 2015 | STLC | No | None (type preservation only) | Yes | CPS, hoisting | Typing by construction (HOAS) | Beluga | n/a |
| Jamner et al., Pyrosome, OOPSLA 2025 | STLC extended to System F with references and recursive functions | Yes | Equational theories | Yes | CPS, others | Equivalence preservation | Coq | ? |
| Minamide, Morrisett, Harper, POPL 1996 | Typed λ (simple and polymorphic) | ? | Operational | Yes (typed, existentials) | — | Type-indexed LR | No (paper) | ? |
| Ahmed & Blume, ICFP 2008 | System F with existential and recursive types | Yes | Operational | Yes | — | Step-indexed LR plus back-translation (full abstraction) | No (paper) | Yes |
| Perconti & Ahmed, ESOP 2014 | Typed language with recursion | Yes | Operational, multi-language | Yes | Two-pass compiler, including CC | Step-indexed LR over a multi-language | ? | ? |
| Bowman & Ahmed, PLDI 2018 | Calculus of Constructions | No (normalizing) | Type-theoretic | Yes (type-preserving) | — | Model of CC-CC in CC | ? | n/a |
| Sullivan, Downen, Ariola, PPDP 2023 | Call-by-push-value | ? | Equational theory plus abstract machine | Yes (as β/η steps) | — | Soundness of equational theory; LR for the machine | ? | ? |
| Wand & Steckler, POPL 1994 / TOPLAS 1997 | Untyped (Scheme-like) | Yes | Operational (labelled transition system) | Yes (selective, lightweight) | — | Flow-analysis constraints | No (paper) | ? |
| Biernacki & Polesiuk, OlivierFest 2025 | Untyped CBV λ with call/cc and abort | Yes | Operational | No (CPS translation) | — | Untyped step-indexed LR, defined by eliminators | ? | Yes |

**How this project differs.** It is the only row that combines all of the following:
- an untyped, Turing-complete source;
- closure conversion;
- denotational semantics on both sides;
- mechanization.

The other denotational rows each lack something:
- Chlipala 2007 is typed and total.
- Benton–Hur is denotational only on the source side, and its compiler does no closure conversion.
- Nielsen is typed and does defunctionalization rather than closure conversion.

Every mechanized untyped closure-conversion proof in the table is operational.

---

## 1. Closure conversion proved correct with denotational semantics

- **Chlipala, "A Certified Type-Preserving Compiler from Lambda Calculus to Assembly Language", PLDI 2007.** [read §2, §7]
  <https://adam.chlipala.net/papers/CtpcPLDI07/CtpcPLDI07.pdf>
  - **What it is.** A Coq compiler for STLC in CPS form, with closure conversion to a language `CC` that has code pointers and environment records. Every intermediate language is given a denotational semantics into Coq types; the low-level languages use coinductive traces.
  - **Proof method.** Correctness uses logical relations "defined recursively on type structure", with existential witnesses at function type, in the style of Plotkin 1973.
  - **Junk is acknowledged and sidestepped.** §7 says the semantics are not fully abstract because target domains "allow more behavior" than the source; for example, function spaces range over all Coq functions. That this is acceptable is "borne out by our success in using this logical relation to prove a final theorem whose statement does not depend on such quantifications."
  - **Relevance.** This is the same junk-entry phenomenon as `blog/stuck.md`. Typing makes the relation definable by induction on types.
  - **Caveat: not a precedent for the hard parts.** The source is STLC, which is total and not Turing complete, and the `CC` pass is typed and total. Denotations are plain Coq functions, so there are no recursive domains and no divergence. Non-termination appears only later, at the `Alloc` stage, through coinductive traces. Chlipala's untyped follow-up (POPL 2010, section 3) is operational.

- **Siek, "Help! We're Failing to Prove Correctness of Closure Conversion using Denotational Semantics (Graph Models)", blog post, June 2023.** [read, including comments]
  <http://siek.blogspot.com/2023/06/help-were-failing-to-prove-correctness.html>
  Suggestions from the comments:
  - **gasche:** use a logical relation, not equality.
  - **Neel Krishnaswami:** follow Minamide–Morrisett–Harper; logical relations are easier over denotations than over terms.
  - **Max (relayed):** Pitts, "Relational Properties of Domains".
  - **An anonymous commenter:** Pitts's Thm 6.5 is the untyped case. For background they recommend Smyth–Plotkin, and Abadi–Plotkin "A PER Model of Polymorphism and Recursive Types" for existentials.

- **TYPES mailing list thread, 2018: "correctness of closure conversion for untyped lambda calculus wrt. denotational semantics".** [abstract: snippets only; the archive pages now return 404]
  <https://lists.seas.upenn.edu/pipermail/types-list/2018/002074.html> (and nearby message numbers)
  - Jeremy Siek's query. The replies point to Chlipala 2007 and Minamide–Morrisett–Harper.
  - Gabriel Scherer observed that natural denotational semantics tend to be fully abstract, so an on-the-nose equation fails. He described Chlipala's statement as a heterogeneous logical relation between source and target denotations.
  - Siek clarified that he meant whole-program correctness, not full abstraction.

- **Nielsen, "A Denotational Investigation of Defunctionalization", BRICS RS-00-47, 2000.** [read 2026-10-16, `related-denot/nielsen-2000.pdf`]
  <https://www.brics.dk/RS/00/47/>
  - Defunctionalization is closure conversion's first-order cousin (Nielsen's own §1.4 says so, and that closure conversion keeps a closed code pointer where defunctionalization keeps a tag).
  - **Languages.** Source: a simply typed CBV language, `nat | τ→τ`, with `0`, `succ`, `ifz` and recursive function abstractions `fun f x : τ1→τ2 = e` (so general recursion; closed programs of type `nat`). Target: first-order, top-level mutually recursive functions plus algebraic data types, as in Bell–Bellegarde–Hook. Both languages get a standard CBV **denotational semantics in CPOs** (`S[[e]]`, `D[[T[e]]]oφ`), recursion by `fix`, results in `N⊥`. The translation stores the whole environment in the constructed value, and applications become calls to per-type `app` functions.
  - **Theorem 2 (weak correctness).** For any program `p`, `S[[p]] = up(n) ⇒ D[[T[p]]] = up(n)`. That is the **forward direction only**: if the source terminates then so does the target, with the same value. Nothing is proved when the source diverges. In his words: "Eventually, we want to prove full correctness, i.e., semantic equivalence of the two programs" (§1.3). His postlude notes that Banerjee–Heintze–Riecke then gave a complete proof, using operational semantics.
  - **The relation (§6.2, Figure 6).** A type-indexed logical relation between source denotations `S[[τ]]` and target denotations `D[[T[τ]]]o`: `n ≺_nat m iff n = m`; `f ≺_{τ1→τ2} g iff ∀ a ≺_{τ1} b. f a ⊲_{τ2} φ(app_{τ1→τ2}) g b`, where `g` is a target *data value* (a defunctionalized closure) and `app` is the target's apply function; and the lifted relation `x ⊲_τ y iff x = ⊥ ∨ (x = up x′ ∧ y = up y′ ∧ x′ ≺_τ y′)`. So **⊥ is related to everything**, which makes the relation one-sided (a source that diverges says nothing about the target) and makes the set `{f | f ≺ g}` inclusive, so the abstraction case goes by **fixed-point induction** (§6.3, Lemma 5: "we use fixed-point induction over the inclusive set"). Existence is by structural recursion on types (the relation is built by "intersections and inverse images by strict continuous functions of smaller relations", citing Winskel ch. 10); there are no recursive types in the source.
  - **What this means for the delay pass.** In graph-model terms (divergence is ∅), Nielsen's `⊲` is the *preservation* inclusion ⟦src⟧ ⊆ ⟦tgt⟧, not the reflection inclusion ⟦tgt⟧ ⊆ ⟦src⟧. So he did not do the equivalent of our reflection proof for the delay pass. The reverse relation (target defined ⇒ source defined and related) does not contain ⊥, so the fixed-point induction that carries his proof is not available, which is the usual reason reflecting divergence needs a different technique (BHR use a lexicographic induction on unwindings and terms; Stoy and Mulmuley's order-asymmetric predicates are the older version of the same problem). This is an inference from reading the proof, not a statement in the paper.
  - **To do: compare our approximant logical relation with Nielsen's relation and with Pitts's relations** (Part III B1, B2): type-indexed and one-sided with fixed-point induction (Nielsen) against indexed by the depth of a finite approximation of the target and used for reflection (ours); Pitts's minimal-invariant relations for recursive types (the case a type index cannot handle: at μX. X ⇒ Int the application case returns to the same type). Nielsen's source has no recursive types, so his type index is well founded.
  - Not mechanized.

- **Banerjee, Heintze, Riecke, "Design and Correctness of Program Transformations Based on Control-Flow Analysis", TACS 2001, LNCS 2215.** [read 2026-10-16, `related-denot/Banerjee-Heintze-Riecke.pdf`. **What the proof of defunctionalization uses.** Source PCFA, a simply typed CBV PCF with control-flow types and recursion: only a natural (operational) semantics, `(e,γ) ⇓ v` (Table 2). Target: a first-order language with both a natural semantics (Table 5) and a set-theoretic denotational semantics, with recursion as the least fixed point of partial functions (§3); Theorem 3 (Adequacy) says `[[∅ ⊢ e : int]] = n iff (e,∅) ⇓ n` (sketch: induction on the derivation one way, lexicographic induction on unwindings and terms the other). Theorem 5 (Correctness of defunctionalization): `(e,∅) ⇓ n` in the source iff `(let D in e*, ∅) ⇓ n` in the target; proof (a sketch): "using the Adequacy Theorem 3, it is enough to show `(e,∅) ⇓ n` iff `[[∅ ⊢ let D in e*]] = n`", by induction on the source derivation and lexicographic induction in the other direction. So the reasoning relates the source's *operational* evaluation to the target's *denotation*; the source has no denotation, and no relation between two denotations is defined. Flow-based inlining (§5) is then proved by comparing the target denotations of the two translated programs (β-reduction and fixpoint induction on `apply3`) and transferring the result to the source through Theorems 3 and 5. They say the semantics "simplifies some of the proofs … especially those involving data abstraction" and that the target needs "no domain theory or posets … due to the lack of higher-order functions". Same-pass summary: They say the earlier proofs by Wand and co-authors use special-purpose operational semantics and prove one direction only. Paper proofs, one pass, no closure conversion proper.]
  <https://link.springer.com/chapter/10.1007/3-540-45500-0_21>
  - Proves defunctionalization correct, then uses that proof to prove flow-based inlining and lightweight defunctionalization correct.
  - The abstract does not say whether the method is denotational; check the full text.

- **Wand and collaborators: denotational and "almost-denotational" proofs of closure-related transformations.** [abstract]
  Index: <https://www.khoury.northeastern.edu/home/wand/analysis-papers.html>
  - Wand, "Correctness of Procedure Representations in Higher-Order Assembly Language", MFPS 1991, LNCS 598.
  - Wand & Steckler, "Selective and Lightweight Closure Conversion", POPL 1994; journal version Steckler & Wand, TOPLAS 1997 [read the journal version, 2026-10-16; the POPL 1994 paper (`related-denot/Wand-POPL-1994.pdf`) has the same untyped source and says "because we deal directly with operational semantics, we avoid any domain-theoretic difficulties"; `related-denot/steckler-wand-1997.pdf`]. Source: an untyped λ-calculus with integers, booleans, conditionals and primitives. Semantics: operational (a big-step evaluator that carries occurrence information, an abstract execution given as a labelled transition system, and an equational reasoning system `=_w`, Theorem 9.1 "Coevaluation"). Correctness (Theorem 11.2) is a commuting diagram of evaluations, in the style of partial correctness (§12: "we do not assume termination of annotated programs"). Paper proofs. Not denotational; one pass.
  - Wand & Sullivan, "Denotational Semantics Using an Operationally-Based Term Model", POPL 1997.
  - Sullivan & Wand, "Incremental Lambda Lifting: An Exercise in Almost-Denotational Semantics", manuscript, 1996.
  - Steckler's thesis, "Correctness of Higher-Order Program Transformations", Northeastern 1994.

- **Hannan, "Type Systems for Closure Conversions", 1995.** [abstract]
  <http://web.cs.ucla.edu/~palsberg/tba/papers/hannan-tpa95.pdf>
  - Closure conversion specified as deductive systems in LF/Elf.
  - The paper notes that an operational semantics for the closure language would be needed to characterize correctness fully.

- **Sullivan, Downen, Ariola, "Closure Conversion in Little Pieces", PPDP 2023.** [abstract] <https://pauldownen.com/publications/cbpvcc.pdf>
  **Sullivan, "Reflections of Closures", PhD thesis, U. Oregon 2023.** [abstract] <https://www.cs.uoregon.edu/Reports/PHD-202311-Sullivan.pdf>
  - Closure conversion is broken into small steps, each an instance of β/η axioms in a calculus with delayed runtime environments. Correctness follows from soundness of that equational theory.
  - The "delayed environments" idea is related to the delay pass here.

## 2. Typed closure conversion, full abstraction, and why junk matters

- **Minamide, Morrisett, Harper, "Typed Closure Conversion", POPL 1996.** [abstract]
  <https://sv.c.titech.ac.jp/minamide/papers/popl96.pdf>
  - Closures are given existential type ∃env. (code × env).
  - Correctness is proved with logical relations, operationally.
  - The existential is what stops contexts from applying code to a foreign environment.

- **Ahmed & Blume, "Typed Closure Conversion Preserves Observational Equivalence", ICFP 2008.** [abstract]
  <https://www.icfpconference.org/icfp2008/accepted/75.html>
  - Proves full abstraction.
  - Methods: a step-indexed logical relation, plus back-translation wrappers.

- **New, Bowman, Ahmed, "Fully Abstract Compilation via Universal Embedding", ICFP 2016.** [abstract] Tech report: <https://williamjbowman.com/resources/fabcc-techrpt.pdf>
  - Includes closure conversion and back-translation sections.

- **Bowman & Ahmed, "Typed Closure Conversion for the Calculus of Constructions", PLDI 2018.** [abstract] <https://arxiv.org/pdf/1808.04006>
  - Type preservation for dependent types.
  - Proof method: a model of the target language CC-CC inside CC.

- **Perconti & Ahmed, "Verifying an Open Compiler Using Multi-Language Semantics", ESOP 2014.** [abstract] <https://www.ccs.neu.edu/home/amal/papers/voc-tr.pdf>
  **Mates, Perconti, Ahmed, "Under Control: Compositionally Correct Closure Conversion with Mutable State", PPDP 2019.** [abstract]
  - Both use multi-language semantics and logical relations for typed closure conversion.

- **Patterson & Ahmed, "The Next 700 Compiler Correctness Theorems (Functional Pearl)", ICFP 2019.** [abstract] <https://www.ccs.neu.edu/home/amal/papers/next700ccc.pdf>
  - A framework for comparing compiler-correctness statements. Useful for stating the end theorem of this project.

- **Morrisett, Walker, Crary, Glew, "From System F to Typed Assembly Language", TOPLAS 1999.** [known]
  - Type-preserving closure conversion as one stage of a typed compiler.

- **Guillemette & Monnier, "A Type-Preserving Closure Conversion in Haskell", Haskell Workshop 2007.** [known]
  - Type preservation enforced by GADTs.

## 3. Mechanized closure conversion (any semantics)

- **Paraskevopoulou & Appel, "Closure Conversion is Safe for Space", ICFP 2019.** [abstract]
  <https://www.cs.princeton.edu/~appel/papers/safe-closure.pdf>
  - Coq, part of CertiCoq: flat closure conversion for an untyped CPS λ-calculus.
  - Proof method: a step-indexed logical relation over profiling semantics. It shows semantics preservation plus time and space safety.
  - Thesis: Paraskevopoulou, "Verified Optimizations for Functional Languages", Princeton 2020, <https://zoep.github.io/thesis_final.pdf>.

- **Paraskevopoulou, Li, Appel, "Compositional Optimizations for CertiCoq", ICFP 2021.** [abstract]
  <https://www.cs.princeton.edu/~appel/papers/comp-opt-certicoq.pdf>
  - Untyped pipeline including closure conversion.
  - Step-indexed logical relations that compose across passes and preserve divergence.

- **Owens, Norrish, Kumar, Myreen, Tan, "Verifying Efficient Function Calls in CakeML", ICFP 2017.** [abstract] <https://www.cl.cam.ac.uk/~mom22/icfp17.pdf>
  **Tan et al., "The Verified CakeML Compiler Backend", JFP 2019.** [abstract]
  - HOL4. The ClosLang intermediate language and the closure-conversion pass `clos_to_bvl` are proved correct with functional big-step semantics using clocks.

- **Neis, Hur, Kaiser, McLaughlin, Dreyer, Vafeiadis, "Pilsner: A Compositionally Verified Compiler for a Higher-Order Imperative Language", ICFP 2015.** [abstract] <https://plv.mpi-sws.org/pils>
  - Coq, about 55K lines. ML-like source to assembly, using parametric inter-language simulations.
  - Builds on Hur & Dreyer, "A Kripke Logical Relation between ML and Assembly", POPL 2011 [known].

- **Wang & Nadathur, "A Higher-Order Abstract Syntax Approach to Verified Transformations on Functional Programs", ESOP 2016.** [abstract] <https://arxiv.org/pdf/1509.03705>
  **Wang, PhD thesis, U. Minnesota, 2017.** [abstract] <https://arxiv.org/pdf/1702.03363>
  - λProlog plus Abella. Typed closure conversion and code hoisting.
  - Semantics preservation via step-indexed logical relations.

- **Savary Bélanger, Monnier, Pientka, "Programming Type-Safe Transformations Using Higher-Order Abstract Syntax", CPP 2013; journal version JFR 8(1), 2015.** [abstract] <https://jfr.unibo.it/article/view/5122>
  - Beluga: type-preserving CPS, closure conversion and hoisting for STLC.
  - Type preservation only, not semantic correctness.

- **Jamner, Kammer, Nag, Chlipala, "Pyrosome: Verified Compilation for Modular Metatheory", OOPSLA 2025.** [abstract] <https://arxiv.org/abs/2507.06360>
  - Coq. An extensible multipass compiler from System F with references, through CPS and closure conversion.
  - Correctness via equational theories, with equivalence preservation.

- **Okuma & Minamide, "Executing Verified Compiler Specification", APLAS 2003.** [abstract; title from memory]
  <https://sv.c.titech.ac.jp/minamide/papers/aplas03.pdf>
  - Isabelle/HOL compiler specification that includes a closure-conversion phase.
  - The extent of the semantic proofs is not confirmed.

- **Danielsson, "Operational Semantics Using the Partiality Monad", ICFP 2012.** [read §1, §5–8] <https://www.cse.chalmers.se/~nad/publications/danielsson-semantics-partiality-monad.html>
  - **Agda.** Untyped λ-calculus with constants. The semantics is an environment-and-closure definitional interpreter, `⟦_⟧ : Tm n → Env n → (Maybe Value)⊥`, in the coinductive partiality monad.
  - **The author says it is *not* denotational:** it is "not defined in a compositional way", and the semantic domain is "rather syntactic: it includes closures".
  - **Compiler:** to a Leroy–Grall stack VM. `comp (lam t) c = clo (comp t [ret]) :: c`.
  - **There is no closure conversion.** The VM closure captures the whole environment and is atomic. The `Lambda.Closure.*` module names refer to the closure-based *semantics*, not to closure conversion.
  - **Correctness:** `exec ⟨comp t [], [], []⟩ ≈ (⟦t⟧ [] >>= return ∘ comp_v)`. One weak-bisimilarity statement covers termination, divergence and crashes. Source and VM values are related by a *function* `comp_v`, defined structurally on syntactic closures.
  - **Relevance:** it shows that a semantics with steps makes an untyped compiler-correctness proof tractable in Agda. It does not face the junk or mixed-variance problems.

- **Chlipala, "A Verified Compiler for an Impure Functional Language", POPL 2010.** [read §1–4] <https://adam.chlipala.net/papers/ImpurePOPL10/ImpurePOPL10.pdf>
  - **Coq.** An *untyped* Mini-ML with references and exceptions, compiled to idealized assembly. Passes include CPS conversion and **closure conversion**.
  - Semantics: big-step operational, with PHOAS and a closure heap.
  - **Only terminating programs are covered.** The main theorem is forward: "if (·, e) ⇓ (h, r) then …"; non-termination is ignored.
  - **How it stays well-founded without types or step indices.** Function values are labels into a closure heap. The relation for functions, `H ⊢ Fix(n) ≃ Fix(n')`, requires the code bodies to be *syntactically* compatible (one is the translation of the other) under a context of related variable pairs. This is a simulation over evaluation derivations, not a semantic logical relation, so no mixed-variance definition is needed.

- **Benton & Hur, "Biorthogonality, Step-Indexing and Compiler Correctness", ICFP 2009.** [abstract]
  <https://www.microsoft.com/en-us/research/wp-content/uploads/2016/02/icfp074-benton.pdf>
  - Coq. Relates a *domain-theoretic* denotational semantics of a **simply typed** language with recursion to an SECD-style machine.
  - Uses step-indexed, biorthogonal relations on the machine side.
  - A follow-up treats a polymorphic language: Hur's talk "Logical Relations and Compositional Compiler Correctness" [abstract].

- **Benton, Kennedy, Varming, "Some Domain Theory and Denotational Semantics in Coq", TPHOLs 2009.** [abstract] <https://www.microsoft.com/en-us/research/?p=157673>
  - Coq ω-cpos, including inverse limits for mixed-variance recursive domain equations.
  - Adequate denotational semantics for typed and **untyped** CBV languages. No compiler.

## 4. Logical relations for untyped / recursive settings (defining the relation)

- **Pitts, "Relational Properties of Domains", Information and Computation 127, 1996.** [abstract] <https://www.cl.cam.ac.uk/~amp12/papers/relpod/relpod.pdf>
  - Existence and uniqueness of relations satisfying mixed-variance recursive specifications, via minimal invariance.
  - Thm 6.5 covers the untyped case, per the blog comment.

- **Reynolds, "On the Relation between Direct and Continuation Semantics", ICALP 1974.** [known]
  - Constructs a relation between two different reflexive domains to prove two semantics equivalent. The classic precedent for relating two untyped semantics.

- **Inclusive predicates: Milne & Strachey (1976); Stoy, "The Congruence of Two Programming Language Definitions", TCS 1981 [known]; Mulmuley, *Full Abstraction and Semantic Equivalence*, MIT Press 1987 [abstract].**
  - Predicates connecting two domains, recursively defined.
  - Mulmuley's abstract notes that proving such predicates exist is "the most difficult part" of the method. That difficulty is the same one this project's mixed-variance relation runs into.

- **Smyth & Plotkin, "The Category-Theoretic Solution of Recursive Domain Equations", SIAM J. Comput. 1982;** and **Abadi & Plotkin, "A PER Model of Polymorphism and Recursive Types", LICS 1990.** [known; recommended in the blog comments]

- **Birkedal & Harper, "Relational Interpretations of Recursive Types in an Operational Setting", Information and Computation 1999.** [abstract]
  <https://www.sciencedirect.com/science/article/pii/S0890540199928286>
  - Syntactic minimal invariance.
  - Includes a relational correctness proof of the CPS transformation.

- **Crary & Harper, "Syntactic Logical Relations for Polymorphic and Recursive Types", ENTCS 2007.** [abstract]

- **Appel & McAllester, "An Indexed Model of Recursive Types", TOPLAS 2001** [known]; **Ahmed, "Step-Indexed Syntactic Logical Relations for Recursive and Quantified Types", ESOP 2006** [abstract]; **Dreyer, Ahmed, Birkedal, "Logical Step-Indexed Logical Relations", LICS 2009 / LMCS 2011** [abstract].
  - The step-indexing route. It needs a step to discharge `▷`; see section 5.

- **"Program Equivalence in an Untyped, Call-by-value Lambda Calculus with Uncurried Recursive Functions", arXiv 2208.14260.** [abstract]
  - Coq, for Core Erlang.
  - Reports that Pitts's logical simulation relation "cannot be directly formalised in Coq for an untyped language" because the definitions fail the strict-positivity check. The authors switched to step-indexing.
  - **The same obstacle applies in Agda.** The finite-observation relation in issue #1 avoids it because it is defined by well-founded recursion on observation depth.

- **Pitts, "Step-Indexed Biorthogonality: a Tutorial Example", 2010.** [abstract] <https://www.cl.cam.ac.uk/~amp12/papers/steibt/steibt.pdf>
  - Untyped CBV λ with recursive functions.

- **Biernacki, Polesiuk (and possibly Balík), "Untyped Logical Relations at Work: Control Operators, Contextual Equivalence and Full Abstraction", OlivierFest 2025.** [abstract]
  <https://conf.researchr.org/details/icfp-splash-2025/olivierfest-2025-papers/16/Untyped-Logical-Relations-at-Work-Control-Operators-Contextual-Equivalence-and-Full>
  - Untyped step-indexed relations defined *by eliminators*.
  - Inter-language untyped logical relations prove a CPS translation fully abstract.
  - Note: "defined by eliminators" matches clause (c) of the proposed relation, which inspects closures only through `car ⋆ cdr`.

## 5. Denotations with steps (making `▷` dischargeable)

- **Møgelberg & Paviotti, "Denotational Semantics of Recursive Types in Synthetic Guarded Domain Theory", LICS 2016; journal version MSCS 29(3), 2019.** [abstract] <https://arxiv.org/pdf/1805.00289>
  - Intensional denotations that count unfold/fold steps. Adequacy is proved with a guarded-recursive logical relation, and a further relation recovers extensional equivalence.
  - Predecessors: Paviotti, Møgelberg, Birkedal, "A Model of PCF in Guarded Type Theory", MFPS 2015 [known]; Birkedal, Møgelberg, Schwinghammer, Støvring, "First Steps in Synthetic Guarded Domain Theory", LICS 2011 [known].
  - Relevance: if the graph-model application operator consumed a "later", the bulk relation in `notes.txt` could be discharged as in step-indexing. Agda's `--guarded` mode or the SIL library could host this.
  - **No closure-conversion or compiler-correctness result was found in the guarded line of work.** It proves adequacy, contextual equivalence, type soundness and graduality (Giovannini–New, arXiv 2411.12822). Guarded Interaction Trees (Frumin, Timany, Birkedal, POPL 2024; ESOP 2025 follow-up; <https://arxiv.org/pdf/2307.08514>) give modular denotational semantics in Iris/Coq, with adequacy and cross-language interoperability, but no compiler. [abstract]

- **Danielsson 2012** (section 3) and **Capretta, "General Recursion via Coinductive Types", LMCS 2005** [known].
  - The partiality/delay monad as denotations with steps.
  - `step-indexed/DenotSTLC.agda` in this repo, with denotations of type `ℕ → Maybe`, is in this family.

## 6. Graph models, filter models, intersection types (the "finite observation" view)

- **Abramsky, "Domain Theory in Logical Form", APAL 51, 1991.** [abstract via secondary sources]
  - Compact elements correspond to formulas or types.
  - Under this view, a finite set of graph-model values is an intersection type. The relation `V' ⊳ D` in issue #1 is then a logical relation indexed by target intersection types.

- **Barendregt, Coppo, Dezani-Ciancaglini, "A Filter Lambda Model and the Completeness of Type Assignment", JSL 1983.** [known]
  - Filter models: the meaning of a term is the set of intersection types it can be assigned.

- **Plotkin, "A Set-Theoretical Definition of Application", 1972** [known]; **Scott, "Data Types as Lattices", 1976** [known]; **Engeler, "Algebras and Combinators", 1981** [known]; **Plotkin, "Set-Theoretical and Other Elementary Models of the λ-Calculus", TCS 121, 1993** [known]; **Longo, "Set-Theoretical Models of λ-Calculus: Theories, Expansions, Isomorphisms", APAL 1983** [abstract] <https://www.di.ens.fr/users/longo/files/Set-TheorModelsLamdaCalcul.pdf>
  - Graph models.
  - No work found that relates two graph models by a simulation or logical relation, which is the situation in this project.

- **Ehrhard, "Non-idempotent Intersection Types in Logical Form", FoSSaCS 2020.** [abstract] <https://arxiv.org/pdf/1911.01899>
  - Intersection types as an *indexed* logic over elements of a relational model, including the untyped case.
  - The closest formal relative found for "relations indexed by finite observations".

- **Plotkin, "Lambda-Definability and Logical Relations", memo SAI-RM-4, Edinburgh 1973.** [abstract] Origin of the term "logical relation".

- **de Jong & Escardó: Scott's D∞ in constructive univalent foundations, formalized in Agda (TypeTopology).** [abstract]
  <https://arxiv.org/pdf/2008.01422>, <https://arxiv.org/abs/2407.06952>, <https://arxiv.org/pdf/2407.06956>
  - Relevant if the Pitts route is ever mechanized in Agda: inverse limits and algebraic domains already exist there.

## 7. This group's prior and related work

- Siek, **"Revisiting Elementary Denotational Semantics"**, arXiv 1707.03762. [abstract]
  - Graph models as practical semantics for mechanization and compiler correctness.

- Siek, **"Transitivity of Subtyping for Intersection Types"**, arXiv 1906.09709; see also `papers/LMCS-subtyping-intersections/`. [abstract]
  - Motivated by compiler verification with filter models.
  - Notes that filter models make some optimization equalities fail, e.g. CSE, because function graphs can represent arbitrary relations. This is related to the junk issue.

- **PLFA, "Denotational" chapter** (Siek, Wadler, Kokke). [known] <https://plfa.github.io/20.07/Denotational/>

- Siek, **"Verified Nanopasses for Compiling Conditionals"**, OlivierFest 2025. [abstract]
  - Agda correctness proof for four nanopasses.

## Suggested next reads (highest value first)

1. **Chlipala 2007, §7 and the CC pass.** How exactly the typed relation handles closures; whether the existential witness in the function case is the environment.
2. **Pitts 1996, §6 (Thm 6.5).** Compare the untyped relational specification with the finite-observation relation, to see whether the latter is an instance or genuinely different.
3. **Møgelberg & Paviotti 2019.** Evaluate the "denotations with steps" alternative.
4. **Biernacki–Polesiuk 2025.** Their eliminator-based untyped relations and inter-language relations are the nearest operational analogue of the proposal.
5. **Abramsky 1991 and Ehrhard 2020.** Check whether relations indexed by compact elements or intersection types already appear in this form.
6. **Nielsen 2000 and Banerjee–Heintze–Riecke 2001.** Denotational proofs for defunctionalization. (BHR read 2026-10-16: denotational for the target only; Nielsen still unread.)


---

# Part III. Logical relations over finite elements, recursive domains, and denotation-to-denotation relations

(The notes of 2026-10-14; formerly `related-work-literature.md`.)

Legend: **[V]** = verified against the primary source text (quote given where possible);
**[U]** = unverified (secondary source or memory). "unverified" for any number not seen.

Our R, as a reminder: R V D relates a FINITE target approximation V (list of finite
graph-model values) to an ARBITRARY source denotation D ∈ 𝒫 Value; function case uses the
source model's own application D ● E; defined as a tower R′ 0 = ⊤, R′ (suc k) = Obs (R′ k),
R V D = R′ (suc (depth V)) V D, with index irrelevance above depth. Purpose: correctness of
the compiler pass delay (Clos3 → Clos4). Category: **B** (denotation-to-denotation).

Classification used throughout:
- **(A)** relation between a denotation (or finite elements/tokens/types of one) and
  syntax / an operational semantics / machine code — adequacy, computability, realizability.
- **(B)** relation between two denotational semantics, or within domains (D×D, D×D′).

---------------------------------------------------------------------------------------------

## Name check (candidate names for our R)

**Method.** I ran web searches (standard and extended) for the exact phrases and close
variants. I queried the arXiv API (abstracts) for `finitary AND logical AND relations`, for
`approximant AND "logical relation"`, and for `approximants AND "logical relations"`. I read the
full text of Jung–Tiuryn 1993 (author PostScript) and the O'Hearn–Riecke 1995 abstract (from
the Syracuse repository page). Semantic Scholar was rate-limited (HTTP 429) and DBLP returned a
bot challenge (HTTP 202), so **no DBLP, ACM DL or Google Scholar full-text search was
completed**. Absence of hits is therefore weak evidence. The author should run one Google
Scholar query for each exact phrase before submission.

### 1. "finitary logical relation(s)"

Exact phrase **not found** anywhere: web search (two variants), arXiv abstracts, Jung–Tiuryn
full text.

Near hits, all in the **same community** (PCF full abstraction and λ-definability) and all
with a **different meaning**:
- **O'Hearn & Riecke**, "Kripke Logical Relations and PCF", *Information and Computation*
  120(1):107–116, 1995, doi:10.1006/inco.1995.1103. Abstract [V, repository page]: "Sieber has
  described a model of PCF consisting of continuous functions that are invariant under certain
  (finitary) logical relations, and shown that it is fully abstract for closed terms of up to
  third-order types. We show that one may achieve full abstraction at all types using a form
  of 'Kripke logical relations' introduced by Jung and Tiuryn to characterize λ definability."
  Here "(finitary)" means **of finite arity** (n-ary relations, Sieber's sequentiality
  relations). Only the abstract was read [V]. Whether the body uses "finitary logical
  relations" as a term is [U].
- **Sieber**, "Reasoning about sequential functions via logical relations", in Fourman,
  Johnstone & Pitts (eds.), *Applications of Categories in Computer Science*, LMS Lecture Note
  Series 177, CUP 1992, pp. 258–269 [U: bib from secondary sources]. These are the relations
  O'Hearn–Riecke call finitary. Whether Sieber himself says "finitary" is [U].
- **Jung & Tiuryn**, "A New Characterization of Lambda Definability", TLCA 1993, LNCS 664,
  pp. 245–257 [V, author bib file]. The full text uses "Kripke logical relations with varying
  arity" and **never** "finitary" [V, grep of the full text, allowing for lost fi-ligatures].
- **"Finitary PCF"** is an established term in the same area: PCF over finite base types
  (Jung & Stoughton, TLCA 1993 [U]; Loader, "Finitary PCF is not decidable", TCS 266, 2001
  [U: title seen in search results; volume from memory]).

What "finitary" commonly means (general knowledge, [U] as to any particular source):
- *Finitary relation*: a relation of finite arity (Wikipedia "Finitary relation"; seen in
  search).
- *Finitary functor or monad*: preserves filtered colimits (Lawvere theories, algebraic
  theories).
- *Finitary projection*: in domain theory, a projection whose image is a (Scott/algebraic)
  domain; this underlies Amadio–Bruce–Longo's "finitary projection model" of polymorphism
  (LICS 1986) [U].
- Mulmuley's 1985 inclusive-predicate theory represents domains as **finitary projections** on
  Scott's universal domain [V, CMU-CS-85-149]. That puts the overload inside the B-relation
  literature itself.
- *Finitary semantics*: finite models (e.g. Grellois–Melliès, "Finitary semantics of linear
  logic and higher-order model-checking", arXiv:1502.05147 [V, title seen]).
- *Finitary vs. infinitary*: λ-calculus, logic.

**Risk.** In the most relevant reader population (logical relations and domain theory),
"finitary logical relations" is most likely to be read as **finite-arity** relations
(Sieber/O'Hearn–Riecke) or associated with **finitary PCF**. Neither matches our meaning
(binary; recursion on a finite approximant). The phrase is not a coined term, so there is no
priority clash, but the overload risk is **moderate to high** for PCF-semantics referees. If
used, define it in the first sentence and contrast it with finite-arity relations in a
footnote.

**Verdict: usable but overloaded.** There is no prior use as a name, and a known parenthetical
use in O'Hearn–Riecke has a different meaning (finite arity).

### 2. "approximant logical relation(s)"

Exact phrase **not found**: web search, and arXiv abstracts for approximant(s) + logical
relation(s). There were no exact hits for "approximant relation" in a semantics sense either.

The word "approximant(s)" already carries established meanings nearby:
- **Wadsworth/Böhm-tree approximants**: approximate normal forms, the "Approximation Theorem"
  for intersection types. Example [V, seen in search]: van Bakel's survey "Strict Intersection
  Types for the Lambda Calculus" defines approximants via λ⊥-normal forms, with the
  Approximation Theorem relating types of a term to types of its approximants.
- **Kleene/fixpoint approximants** f^n(⊥) and **syntactic approximants** fix^n in operational
  reasoning (Pitts-style "approximation lemma") [U].
- **Finite elements** of a domain, as approximants of an element [general usage].

Our sense ("a finite approximant of the target denotation") is close to the fixpoint/Böhm
sense. That is a natural fit rather than a clash, but intersection-type readers may expect
Wadsworth approximants (terms).

**Risk: low to moderate.** No prior name use was found.

**Verdict: safer, no prior use found.** It describes the asymmetric, finite-side indexing
better than "finitary". Its main drawback is a mild collision with Wadsworth "approximants"
(which are terms, not values).

---------------------------------------------------------------------------------------------

## PART A — Relations for adequacy / computability (denotation vs. syntax or operations)

### A1. Winskel 1993, *The Formal Semantics of Programming Languages*, ch. 13

```bibtex
@book{Winskel93,
  author    = {Glynn Winskel},
  title     = {The Formal Semantics of Programming Languages: An Introduction},
  publisher = {MIT Press},
  address   = {Cambridge, MA},
  series    = {Foundations of Computing},
  year      = {1993}}
```

Location **[V]** (read from a scanned copy of the 1993 MIT Press edition; table of contents
and running heads):
- Chapter 13 "Recursive types" (starts p. 251).
- §13.4 "Adequacy of eager semantics", pp. 262–267. **Lemma 13.7** (p. 264) — the claim
  "§13.4, Lemma 13.7" is **correct**. Lemma 13.8 (pp. 264–265) is the entailment/up-closure
  property; Theorem 13.9 (p. 265) is adequacy (t⇓ denotationally ⇒ t⇓ operationally);
  Corollary 13.11.
- §13.9 "Adequacy of lazy semantics" (p. 288): **Lemma 13.30** (pp. 288–289) is the lazy
  analogue, Lemma 13.31 the entailment property. **The lazy proof uses the same method** [V].
- Caveat [U]: a secondary listing (2001 printing, Japanese bibliographic page) shows different
  chapter numbering; cite the 1993 edition explicitly.

What is related **[V]**: tokens of the information system V_τ (finite syntactic objects; for
function types a token is a pair (U, V) of finite token sets) and closed canonical forms C_τ.
Quote (Lemma 13.7, OCR-cleaned):
> "For each closed type τ there is a relation ⊑_τ between tokens of V_τ and canonical forms
> C_τ with the following properties: ∅ ⊑_1 (); (a,b) ⊑_{τ1*τ2} (c1,c2) iff a ⊑_{τ1} c1 &
> b ⊑_{τ2} c2; (U,V) ⊑_{τ1->τ2} λx.t iff ∀c ∈ C_{τ1}. U ≲_{τ1} c ⇒ V ≲_{τ2} t[c/x];
> (1,a) ⊑ inl(c) iff a ⊑ c; (2,b) ⊑ inr(c) iff b ⊑ c; a ⊑_{μX.τ} abs(c) iff
> a ⊑_{τ[μX.τ/X]} c, where we write U ≲_τ s ... iff ∀b ∈ U ∃c ∈ C_τ.(b ⊑_τ c & s → c)."

(The relation symbol is garbled by OCR; it is an ⊑/≲-style symbol. The element-level relation
d ≲_τ t for d ∈ |V_τ⊥| is derived from the token relation.)

Recursion principle **[V]**:
> "We can no longer do this when types can be defined recursively; the definition of
> ≲_{μX.τ} cannot be given straightforwardly in terms of ≲_{τ[μX.τ/X]} as such a definition
> would not be well-founded. Fortunately we can still give a simple definition of the
> relations ≲_τ by taking advantage of the information-systems representation."
> Proof of 13.7: "The relation ⊑ exists by well-founded recursion on the size of tokens and
> canonical forms combined lexicographically", with size(∅)=1, size(X)=1+Σ_{a∈X} size(a),
> size((a,b))=1+size(a)+size(b), etc.
(For the lazy Lemma 13.30: "well-founded recursion on the size of tokens and the structure of
canonical forms ordered lexicographically".)

Model **[V]**: Scott information systems (consistency + entailment), with recursive types
solved inside information systems. Purpose: computational adequacy of eager (and lazy)
denotational semantics w.r.t. big-step evaluation. In ch. 11 (§11.4, "Agreement of eager
semantics", p. 190) — no recursive types — the relation is by structural induction on types
[V, as stated in §13.4].

Credits **[V]** (§13.11 "Further reading", p. 295): "The technique used in proving adequacy
follows closely that in Gordon Plotkin's lecture notes—similar methods of proof have been used
by Per Martin-Löf in his domain interpretation of type theory (1983), and by Samson Abramsky
[1]." ([1] = Abramsky, "The lazy lambda calculus".) Martin-Löf has **no** bibliography entry
in Winskel [V]. Which Plotkin notes are meant is not given in that sentence (candidates in the
bibliography: [80] "The Pisa lecture notes", [83] "Types and partial functions", CSLI 1985)
— unverified which.

Relation to our R: closest *technical* ancestor for "recursion on the size of a finite
function token (U,V)" — Winskel's function token is a finite input/output pair just like an
entry of our finite tables. But it is category **A** (token vs canonical term), symmetric only
in the sense of being finite-vs-syntax, and needs no step tower because the recursion is
well-founded on token size; we instead use a depth-indexed tower because the right-hand side
is an arbitrary (possibly infinite) set, not syntax.

### A2. Martin-Löf 1983, "Lecture notes on the domain interpretation of type theory"

```bibtex
@misc{MartinLof83,
  author       = {Per Martin-L{\"o}f},
  title        = {Lecture Notes on the Domain Interpretation of Type Theory},
  howpublished = {In Programming Methodology Group (ed.), Workshop on the Semantics of
                  Programming Languages, Chalmers University of Technology, G{\"o}teborg},
  year         = {1983},
  note         = {Handwritten notes; scan: archive-pml.github.io, file
                  Notes-on-The-Domain-Interpretation-of-Type-Theory-1983.pdf}}
```
Bibliographic form **[V]** as cited in Abramsky's thesis (arXiv:1112.0347, entry [Mar83]):
"P. Martin-Löf. Lecture notes on the domain interpretation of type theory. In Programming
Methodology Group, editor, Workshop on the Semantics of Programming Languages, Chalmers
University of Technology, Göteborg, Sweden, 1983." The scan (title page "Notes on The Domain
Interpretation of Type Theory by Per Martin-Löf", 11 scanned sheets, handwritten pages
numbered 1–39, followed by a typed "Discussion during Per Martin-Löf's talk") was read
visually **[V]**.

Content **[V]** (from the handwritten scan; section numbers are Martin-Löf's own):
1. "Computation rules" — big-step evaluation c ⇒ e for an untyped language of type-theory
   program forms (λ, ap, pairs/E, inl/inr/D, finite sets m_n, 0/s/R, sup/T, ω, omegarec, fix).
2. "(Formal) neighbourhoods" — syntactic finite elements built by finite intersection,
   λ(∩_{i∈I}[U_i,V_i]) (function neighbourhoods as finite intersections of step-function
   neighbourhoods), (U,V), i(U), j(V), s(U), sup(...). Then:
   > "Definition of the relation Approx(a, U) ≡ a ∈ U which says that a formal neighbourhood
   > U approximates a program a."
   given by inference rules, e.g. "c ⇒ λ(b), b(x) ∈ V_i (x ∈ U_i) / c ∈ λ(∩[U_i,V_i])"
   (hypothetical premise: for x ∈ U_i, b(x) ∈ V_i), "c ⇒ (a,b), a ∈ U, b ∈ V / c ∈ (U,V)".
   With every program a he associates "the operational neighbourhood filter ã = {U | a ∈ U}".
3. Formal inclusion and consistency (decidable) and a theorem that formal inclusion implies
   ∀x(x ∈ U ⊃ x ∈ V).
4. "Denotational semantics" — "a neighbourhood filter" (up-closed, ∩-closed, consistent); "By
   induction on its construction, I associate with a program a its denotation â, which is a
   neighbourhood filter"; an open program b(x1..xn) denotes an (n+1)-ary relation between
   neighbourhoods U1,…,Un b̂ V (i.e. an approximable mapping / graph on finite elements).
5. "First theorem. If a ⇒ b, then â = b̂."
6. "Second theorem. For an arbitrary program a, â ⊆ ã. That is, a denotational neighbourhood
   of a program is always an operational neighbourhood of the same program. U ∈ â → U ∈ ã ≡
   a ∈ U. Proof. By induction on the construction of the program a." Followed by a
   Corollary: ĉ = {Δ} ⟺ c does not terminate.

Classification: **A** (formal neighbourhood = finite element vs. program). Recursion
principle: inductive definition by rules indexed by the syntactic structure of the formal
neighbourhood (the relation for λ(∩[U_i,V_i]) refers to U_i, V_i only), so it is well-founded
even though the language is untyped and the domain is reflexive. Purpose: adequacy (agreement
of denotational and operational semantics) for the program forms of (partial) type theory.
Note **[V]**: there is no size measure in the notes; the well-foundedness comes from the
inductive syntax of neighbourhoods (Winskel later phrases it as recursion on token size).

Relation to our R: the true origin of "define the approximation relation only on finite
elements, by induction on their syntax, then lift to arbitrary elements by the filter/closure
property". Like ours, the λ clause quantifies over all arguments approximated by U_i; unlike
ours, the other side is a program, not a denotation, and his relation is purely inductive
(no index).

### A3. Pitts 1996 §5 (and Pitts 1993 MFPS) — the domain-vs-syntax part
See B1/B2 below for full bibliographic data; the formal-approximation relation of §5 is
category **A**: ◁_σ ⊆ D × Can_σ (domain elements vs canonical forms) **[V]**.

### A4. Abramsky

#### A4a. Abramsky, "The Lazy Lambda Calculus" (1990)
```bibtex
@incollection{Abramsky90,
  author    = {Samson Abramsky},
  title     = {The Lazy Lambda Calculus},
  booktitle = {Research Topics in Functional Programming},
  editor    = {David A. Turner},
  publisher = {Addison-Wesley},
  pages     = {65--117},
  year      = {1990}}
```
Pages: 65–117 per Abramsky's Oxford publication page [V]; Pitts 1996's bibliography says
65–116 [V]. Check the physical book before choosing. Text read from the author's re-typeset
PDF (cs.ox.ac.uk/files/293/lazy.pdf, dated 2006), so page numbers there differ from the book.
Result numbers below were checked in that PDF [V].
- §5 "A Domain Logic for Applicative Transition Systems": L ::= t | φ∧ψ | (φ→ψ)⊥.
  **Definition 5.2** (satisfaction, by structural recursion on formulas) [V]: "a ⊨_A (φ → ψ)⊥ ≡
  a⇓f & ∀b ∈ A. b ⊨_A φ ⇒ f(b) ⊨_A ψ". Lemma 5.3 (applicative bisimulation ⊆ ⊑_L) is proved
  "by induction on φ".
- Theorem 5.8 (Soundness of the program logic), Theorem 5.14 (D is L-complete, via DTLF Stone
  duality), Theorem 5.17 (D ≅ Filt L), **Theorem 5.18 (Computational Adequacy)**: "For all M ∈
  Λ, M⇓ ⟺ [[M]]^D ρ⊥ ≠ ⊥" [V]. Abramsky's comment [V]: "The triviality of this proof is
  notable, since analogous results in the literature have required lengthy arguments involving
  recursively defined inclusive predicates (cf. [Plo85])."
- Method: satisfaction of a formula (a syntactic name for a compact element of D = (D→D)⊥)
  by a term in the operational term model, by induction on formulas. Soundness is the
  formula-induction step. Completeness of the logic for D (Stone duality) moves the hard part
  into the logic. Classification **A**. Recursive domain handled by the logic (formulas =
  compact opens) rather than by a recursively specified relation.
- Relation to our R: also a "finite-syntactic-element vs. arbitrary thing" relation by
  structural induction on the finite side, but the arbitrary thing is a term in a transition
  system, not a second denotation.

#### A4b. Abramsky & Ong 1993
```bibtex
@article{AbramskyOng93,
  author  = {Samson Abramsky and C.-H. Luke Ong},
  title   = {Full Abstraction in the Lazy Lambda Calculus},
  journal = {Information and Computation},
  volume  = {105},
  number  = {2},
  pages   = {159--267},
  year    = {1993},
  doi     = {10.1006/inco.1993.1044}}
```
Bibliographic data [V] (Crossref; Pitts 1996's bibliography also says 159–267; the Oxford page
says 159–268). Proof method **[V]**, read from `related-denot/abramsky-1993.pdf`
(image-only scan, read page by page; journal page numbers as printed). Same method as LLC (A4a),
§5 "A Domain Logic for Applicative Transition Systems", pp. 197–207:
- Domain logic L ::= t | φ∧ψ | (φ→ψ)⊥ with satisfaction over any q-ats by recursion on formulas:
  "a ⊨ (φ → ψ)⊥ ≡ a⇓f & [∀b ∈ A. b ⊨ φ ⇒ f(b) ⊨ ψ]" (Def. 5.2.2, p. 198); λ ≡ (t → t)⊥ and
  "a⇓ ⟺ a ⊨ λ".
- A program logic M, Γ ⊢ φ (intersection-type-like rules), with Theorem 5.3.3 (Soundness of
  Program Logic), "M, Γ ⊢ φ ⇒ M, Γ ⊨ φ" for every lazy λ-model, "proof is again routine" (pp.
  201–202). Theorem 5.4.6: "D is L-complete", via Stone duality (D ≅ Filt(L)) and the
  completeness theorem of DTLF [Abr87c] (p. 204). Proposition 5.4.8: Filt(L) is an lts
  isomorphic to D, and "[[M]]^D_ρ" corresponds to "[[M]]^{Filt L}" (p. 205).
- **Theorem 5.4.9 (Computational Adequacy)**, p. 206: "For all M ∈ Λ°, M⇓ ⟺ D ⊨ M⇓ (i.e.,
  [[M]]^D ≠ ⊥)". Proof: "⇒" "follows immediately from D being a lazy λ-model"; for "⇐",
  [[M]]^D ≠ ⊥ ⇒ [[M]]^{Filt L} ≠ {t} ⇒ M ⊢ λ ⇒ M ⊨ λ (Theorem 5.3.3, in the term model) ⇒ M⇓.
  Comment (p. 206): "The triviality of this proof is notable, since analogous results in the
  literature have required lengthy arguments involving recursively defined predicates (cf.
  (Plo85))."
- What is related to what: formulas (names of compact elements of D) to elements of an
  applicative transition system, here closed terms of the operational model; no relation between
  terms and arbitrary domain elements is defined. Classification **A**; the hard part
  (recursive domain) is moved into the completeness of the logic.
Ong's 1988 Imperial PhD thesis has "§3.2.3 A General Adequacy Result" for continuous lazy
λ-models [V title only, method unseen].

#### A4c. Abramsky, "Domain Theory in Logical Form" (1991)
```bibtex
@article{Abramsky91DTLF,
  author  = {Samson Abramsky},
  title   = {Domain Theory in Logical Form},
  journal = {Annals of Pure and Applied Logic},
  volume  = {51},
  number  = {1--2},
  pages   = {1--77},
  year    = {1991},
  doi     = {10.1016/0168-0072(91)90065-T}}
```
Bibliographic data [V]. Content [V] (thesis version arXiv:1112.0347, Chapter 4): Theorem
4.3.1, soundness and completeness of the endogenous logic, "M, Γ ⊢ φ ⟺ M, Γ ⊨ φ" with
"d ⊨ φ ≡ d ∈ [[φ]]". So the DTLF chapter relates **formulas to denotations** (logic vs. model)
and contains no operational adequacy proof. Classification: neither A nor B in our sense: it
is a logic-vs-model duality, and the adequacy use is in the LLC paper. The thesis cites
Martin-Löf [Mar83] for the term-language constructions [V: "following ideas of Martin-Löf
[Mar83] and Plotkin [Plo85]"].

### A5. Intersection types / filter models
Bibliographic data [V] (Crossref):
```bibtex
@article{BCD83,
  author  = {Henk Barendregt and Mario Coppo and Mariangiola Dezani-Ciancaglini},
  title   = {A Filter Lambda Model and the Completeness of Type Assignment},
  journal = {Journal of Symbolic Logic},
  volume  = {48}, number = {4}, pages = {931--940}, year = {1983},
  doi     = {10.2307/2273659}}
@article{CDV81,
  author  = {Mario Coppo and Mariangiola Dezani-Ciancaglini and Betti Venneri},
  title   = {Functional Characters of Solvable Terms},
  journal = {Zeitschrift f{\"u}r mathematische Logik und Grundlagen der Mathematik},
  volume  = {27}, number = {2--6}, pages = {45--58}, year = {1981},
  doi     = {10.1002/malq.19810270205}}
@book{Krivine93,
  author    = {Jean-Louis Krivine},
  title     = {Lambda-Calculus, Types and Models},
  publisher = {Ellis Horwood}, year = {1993},
  note      = {French original: Lambda-calcul, types et mod{\`e}les, Masson, Paris, 1990}}
```
Krivine [V] from the PDF on Krivine's site. The PDF shows "Paris, 1990". English edition [A, Open
Library record OL7174632W]: *Lambda-Calculus, Types and Models*, Ellis Horwood, 1993, ISBN
0-13-062407-1, 192 pp. The translator and the series are not verified. Cleanest citation for "a relation between intersection types and terms,
by induction on types":
- Krivine, ch. 3 "Intersection type systems" [V]: types are interpreted as saturated sets of
  terms "by induction on the length of A: … |Ω| = Λ; if A = B → C, then |A| = |B| → |C|; if
  A = B∧C, then |A| = |B| ∩ |C|".
- **Lemma 3.5 (Adequacy lemma)** [V]: "If t1 ∈ |A1|,…,tk ∈ |Ak| then u[t1/x1,…,tk/xk] ∈ |A|".
  It is used for Theorem 3.7 (typable with a non-trivial type in DΩ ⇒ head reduction finite).
- The link "types = compact elements of the filter model" comes from BCD83, not from Krivine.
  Krivine's predicate is unary realizability for characterisation, not stated as adequacy of a
  filter model.

Classification **A**. Recursion on the type, which is a finite syntactic object, so reflexive
domains cause no trouble. Abramsky (LLC §5) explicitly notes "the striking similarity of our
program logic with type inference, in particular with the intersection type discipline" [V].

Other candidates, all [U]: Barendregt–Dekkers–Statman, *Lambda Calculus with Types* (CUP
2013), Part III; Egidi–Honsell–Ronchi Della Rocca, "Operational, denotational and logical
descriptions: a case study", Fundamenta Informaticae 16(2):149–169, 1992 (ISWIM/SECD vs. a
filter model; method unseen); Ronchi Della Rocca & Paolini, *The Parametric Lambda Calculus*
(Springer 2004).

Relation to our R: the PLFA/Siek "element-indexed" relations are exactly intersection-type
realizability with types replaced by finite graph values. Ours is the denotation-to-denotation
variant.

### A6. Siek 2017, "Revisiting Elementary Denotational Semantics" (arXiv:1707.03762)

```bibtex
@misc{Siek17,
  author        = {Jeremy G. Siek},
  title         = {Revisiting Elementary Denotational Semantics},
  year          = {2017},
  eprint        = {1707.03762},
  archivePrefix = {arXiv},
  primaryClass  = {cs.PL},
  note          = {v4, 21 Oct 2017}}
```
Title **[V]** (v4). Location **[V]**: §5 "Mechanized Correctness of Elementary Semantics",
§5.1 "Sound with respect to operational semantics"; relation G, Lemma 2 (G downward closed),
Lemma 3, Lemma 4 (main lemma), Theorem 2 "(Sound wrt. op. sem.) (aka. Adequacy)". §6 is the
optimizer (inliner) correctness, Lemma 10 "Optimizer Preserves Denotations", Theorem 5.

What is related **[V]**: a *single finite value* d (integer n or finite table t of pairs
(d1,d2)) and a *set* of syntactic values (closures ⟨λx.e, ϱ⟩ of Kahn's big-step semantics):
> "We relate D to sets of syntactic values V of Kahn [38] with the following logical
> relation. Logical relations are usually type-indexed, not element-indexed, but our domain
> elements are isomorphic to types.
>   G : D → P(V)
>   G(n) = {n}
>   G(t) = {⟨λx. e, ϱ⟩ | ∀(d1,d2)∈t. ∀v1. v1∈G(d1) ⟹ ∃v2. ϱ(x:=v1) ⊢ e ⇒ v2 ∧ v2∈G(d2)}"
So: **yes, the phrase "element-indexed" appears** [V]; G is defined by structural recursion on
the finite value d (Lemma 2 "by induction on d"). Model: Siek's own graph-like model
(values are integers or finite graphs/tables; denotation E⟦e⟧ρ is a set of such values), §3.
Purpose: soundness (adequacy) of the elementary semantics w.r.t. Kahn's big-step semantics;
mechanized in Isabelle. The inliner correctness in §6 is proved by denotational equality +
contextual-equivalence soundness, *not* by a relation between two denotations [V].
Category **A**.

Relation to our R: same family of finite values and the same "relation indexed by a finite
value" idea, but A-type (value vs closure) and symmetric-in-kind; no tower needed because the
other side is syntax and recursion is structural on d.

### A7. PLFA, part 3, chapter "Adequacy" (Siek's chapters in Wadler–Kokke–Siek)

```bibtex
@book{PLFA,
  author = {Philip Wadler and Wen Kokke and Jeremy G. Siek},
  title  = {Programming Language Foundations in {A}gda},
  url    = {https://plfa.github.io/},
  year   = {2022},  % cite the version/date actually used
  note   = {Chapters Denotational, Compositional, Soundness, Adequacy}}
```
Source **[V]**: src/plfa/part3/Adequacy.lagda.md (dev branch), module plfa.part3.Adequacy,
title "Adequacy: Adequacy of denotational semantics with respect to operational semantics".
Model **[V]** (Denotational.lagda.md): `data Value : Set where ⊥ : Value; _↦_ : Value →
Value → Value; _⊔_ : Value → Value → Value` with an ordering `_⊑_` (⊑-bot, ⊑-conj-L, …,
including distributivity); `Denotation Γ = (Env Γ → Value → Set)`, `ℰ M = λ γ v → γ ⊢ M ↓ v`
— a filter-model-style semantics for untyped CBN λ-calculus.
Relation **[V]**:
```agda
𝕍 : Value → Clos → Set
𝔼 : Value → Clos → Set
𝕍 v (clos (` x₁) γ) = Bot
𝕍 v (clos (M · M₁) γ) = Bot
𝕍 ⊥ (clos (ƛ M) γ) = ⊤
𝕍 (v ↦ w) (clos (ƛ N) γ) =
    (∀{c : Clos} → 𝔼 v c → above-fun w → Σ[ c' ∈ Clos ]
        (γ ,' c) ⊢ N ⇓ c'  ×  𝕍 w c')
𝕍 (u ⊔ v) (clos (ƛ N) γ) = 𝕍 u (clos (ƛ N) γ) × 𝕍 v (clos (ƛ N) γ)
𝔼 v (clos M γ') = above-fun v → Σ[ c ∈ Clos ] γ' ⊢ M ⇓ c × 𝕍 v c
```
"We define 𝕍 as a function ... and not as a data type because it is mutually recursive with
𝔼 in a negative position ... If the term is a lambda abstraction, we define 𝕍 by recursion
on the value." Environments: 𝔾 γ γ' = ∀x → 𝔼 (γ x) (γ' x). Main lemma `↓→𝔼`
(γ ⊢ M ↓ v and 𝔾 γ γ' ⇒ 𝔼 v (clos M γ')), `sub-𝕍` (down-closure), `↓→⇓`, and `adequacy`
(ℰ M ≃ ℰ (ƛ N) ⇒ M —↠ ƛ N′). Category **A**: finite Value vs closure of a CBN big-step
semantics; recursion on the structure of the Value (Agda structural recursion).

Relation to our R: the immediate Agda predecessor of our approach (same author lineage,
structural recursion on a finite value); our R replaces the closure side by an arbitrary
denotation of a *second* semantics and so cannot recurse purely on the left finite value
when the right-hand side is applied via D ● E — hence the depth-indexed tower.

### A8. Benton & Hur 2009; Benton & Hur 2010; Benton–Kennedy–Varming 2009; Hur & Dreyer 2011

#### A8a. Benton & Hur, ICFP 2009
```bibtex
@inproceedings{BentonHur09,
  author    = {Nick Benton and Chung-Kil Hur},
  title     = {Biorthogonality, Step-Indexing and Compiler Correctness},
  booktitle = {Proceedings of the 14th ACM SIGPLAN International Conference on
               Functional Programming (ICFP)},
  pages     = {97--108},
  year      = {2009},
  doi       = {10.1145/1596550.1596567}}
```
[V]: author PDF and Crossref. Abstract [V]: "We define logical relations between the denotational
semantics of a simply typed functional language with recursion and the operational behaviour of
low-level programs in a variant SECD machine. The relations, which are defined using
biorthogonality and step-indexing, capture what it means for a piece of low-level code to
implement a mathematical, domain-theoretic function and are used to prove correctness of a
simple compiler."
- Source [V]: PCFv, call-by-value, with `Fix f x = M`. Types are Int, Bool, × and →, so there
  are **no recursive types**. The semantics is in ω-cpos and is computationally adequate.
- Two **asymmetric** relations [V]:
  1. Low-level approximates denotation. This direction is **step-indexed on the machine side**
     and closed by biorthogonality, by induction on types. The arrow case is
     `E^{t→t'}_i = {(f, df) | ∀k ≤ i, ∀(v,dv) ∈ E^t_k, (([App],[v,f]), λ*:1. df dv) ∈ (I → (E^{t'})⊥)_k}`,
     with `v ◁ d ⇔ ∀i, v E^t_i d`.
  2. Denotation approximates low-level. This direction is **not step-indexed**: "We will not
     use operational step-indexing to define the relation this way around, but an explicit
     admissible closure operation will play a similar rôle", because "{d | v D^t d} is not
     always closed under taking limits of chains".
- Theorems 1 and 2 [V] give compiler correctness, one per direction. For Theorem 1, "In the
  case for recursive functions, there is a nested induction over the step indices".
- Classification **A** (domain element vs. machine code). The step index counts machine steps,
  not the depth of a finite element.
- Relation to our R: this is the closest prior "denotation-side vs. other-side, asymmetric,
  step-indexed" design, but the index sits on the operational side. Ours sits on the finite
  target approximation, and both sides are denotations.

#### A8b. Benton & Hur, MSR-TR-2010-62
```bibtex
@techreport{BentonHur10,
  author      = {Nick Benton and Chung-Kil Hur},
  title       = {Realizability and Compositional Compiler Correctness for a Polymorphic
                 Language},
  institution = {Microsoft Research},
  number      = {MSR-TR-2010-62},
  month       = apr,
  year        = {2010}}
```
[V]. **The source semantics is operational, not denotational** [V]: "we work with an
operational, rather than a denotational, semantics for the high-level language".
- Source: Fv, a CBV language with recursion and impredicative ∀ and ∃. It has no recursive
  types; these are listed as future work [V].
- The relations are between SECD components and Fv terms. They are parameterised by an
  abstract approximation relation with axioms that include Unfold (via finite unrollings
  rec^n). The machine side is step-indexed [V].
- Classification **A**.

#### A8c. Benton, Kennedy & Varming, TPHOLs 2009
```bibtex
@inproceedings{BKV09,
  author    = {Nick Benton and Andrew Kennedy and Carsten Varming},
  title     = {Some Domain Theory and Denotational Semantics in {C}oq},
  booktitle = {Theorem Proving in Higher Order Logics (TPHOLs 2009)},
  series    = {LNCS}, volume = {5674}, pages = {115--130}, year = {2009},
  doi       = {10.1007/978-3-642-03359-9_10}}
```
[V]. The development goes "up to and including the inverse-limit construction of solutions to
mixed-variance recursive domain equations, and the existence of invariant relations on those
solutions" (abstract).
- Typed language [V]: `relVal τ : SemTy τ → CValue τ → Prop`, by recursion on types.
- Untyped language, D ≅ (nat + (D →c D))⊥ [V]: "now cannot define the relation by induction on
  types. … Following Pitts [23], however, we again use the technique of separating positive and
  negative occurrences … constructed by Knaster-Tarski. … By applying the minimal invariant
  property … we prove that in fact ∆− == ∆+".
- Classification **A** (adequacy only, no compiler). This is a mechanized instance of Pitts's
  minimal-invariant method.
- An extended draft adds Lars Birkedal as an author: Benton, Birkedal, Kennedy & Varming,
  "Formalizing Domains, Ultrametric Spaces and Semantics of Programming Languages". The PDF
  header says it was under consideration for MSCS, received 12 July 2010 [V]. Final
  publication is [U].

#### A8d. Hur & Dreyer, POPL 2011
```bibtex
@inproceedings{HurDreyer11,
  author    = {Chung-Kil Hur and Derek Dreyer},
  title     = {A {K}ripke Logical Relation Between {ML} and Assembly},
  booktitle = {Proceedings of the 38th ACM SIGPLAN-SIGACT Symposium on Principles of
               Programming Languages (POPL)},
  pages     = {133--146}, year = {2011},
  doi       = {10.1145/1926385.1926402}}
```
[V]. The relation is fully operational: "a biorthogonal, step-indexed, Kripke logical relation"
between a System-F-like language and assembly. The source has iso-recursive types and
references; recursive types are handled by step levels of worlds.
- Their characterisation of Benton–Hur [V]: "These half-operational, half-denotational
  relations were of necessity asymmetric … step-indexing—but only in defining one direction of
  approximation (in the other direction, they use an admissible closure operation)."
- Not A or B in the denotational sense; it is operational-to-operational. It is useful mainly
  as the authoritative statement of Benton–Hur's asymmetry.

---------------------------------------------------------------------------------------------

## PART B — Relations between two denotational semantics / within domains

### B1. Pitts 1996, "Relational Properties of Domains"

```bibtex
@article{Pitts96,
  author  = {Andrew M. Pitts},
  title   = {Relational Properties of Domains},
  journal = {Information and Computation},
  volume  = {127},
  number  = {2},
  pages   = {66--90},
  year    = {1996},
  note    = {Revised version of Univ. Cambridge Computer Laboratory Tech. Rept. 321 (1993);
             preliminary version: Relational properties of recursively defined domains,
             Proc. 8th LICS 1993, pp. 86--97}}
```
**[V]** volume 127, pp. 66–90, 1996 (article no. 0052) from the PDF header; issue number 2 [V, Crossref
record for doi:10.1006/inco.1996.0052, which also gives June 1996].

Structure **[V]**: §1 Introduction; §2 Overview; §3 "Minimal Solutions of Domain Equations" ( Theorem 3.3 existence
of minimal invariants, Theorem 3.4 Freyd's mixed initiality/finality, Example 3.6 the lazy
λ-calculus domain rec α.(α→α)⊥); §4 relational structures (Example 4.2, Definition 4.3
admissible, Definition 4.8 invariant R-relations, **Theorem 4.16 Existence of Invariant
Relations**); **§5 "Computational Adequacy"** (Proposition 5.1, relations ◁_σ, conditions
(17)–(23)); **§6 "Induction and Co-induction Principles"** (Theorem 6.5 induction, Theorem
6.12 co-induction, Corollary 6.13).

The three methods — **[V]**, §5, p. 81 (the claim "§5 names the Martin-Löf method" is
**correct**; there is no bibliography entry for Martin-Löf, and nothing is cited for him):
> "In the literature, two methods can be found for constructing relations on recursively
> defined domains with such nonmonotonic fixed point properties. One method, due to Milne,
> Plotkin, and Reynolds makes use of Scott's construction of a recursively defined cppo as the
> colimit of a chain of embeddings D0 → D1 → ⋯, where the cppo Dn is obtained by iterating the
> domain constructor n times, starting with the trivial cppo {⊥} ... Then the desired relation
> can be constructed as an intersection of countably many relations defined by induction on n
> at the same time as the Dn are defined; see (Reynolds, 1974). A second method, essentially
> due to Martin-Löf, applies only to Scott domains (precluding the use of constructors like
> the Plotkin powerdomain) since it makes use of their presentation in terms of 'information
> systems' (Scott, 1982). This method hinges upon the fact that each {d | d(◁σ)⊥e} is in fact
> a Scott-closed subset of σ. Hence it suffices to construct the relations ◁σ only for
> compact elements of σ ... Information systems provide a formal language for compact
> elements of (recursively defined) Scott domains, and a(◁σ)⊥e (a compact) can be defined by
> a well-founded induction on the size of (a formal representation of) a; see (Winskel, 1993,
> Section 13.4). Here we show that the existence of relations ◁σ satisfying (17)–(23) follows
> directly from Theorem 4.16 ... This provides a new method of construction that is more
> abstract than the above two, in that it relies upon the 'minimal invariant' property of the
> recursively defined cppo ty rather than upon the techniques for giving concrete
> constructions of recursively defined domains."
Cited for the stage method: Milne 1973 (PhD thesis, Cambridge), Plotkin 1973 ("Lambda
Definability and Logical Relations", Memo SAI-RM-4, Edinburgh), Reynolds 1974 [V, intro and
bibliography]. Note: Pitts calls it a "colimit of a chain of embeddings"/"intersection of
countably many relations defined by induction on n"; the phrase "projection-indexed" is ours.

Which relations are A and which B **[V]**:
- §5, (17)–(23): ◁_σ ⊆ σ⊥ × Can_σ (domain element vs canonical form); clause (23)
  "f ◁_{σ→σ'} λx:σ.e ⟺ ∀d,c (d ◁_σ c ⇒ f(d)(◁_{σ'})⊥ e[c/x])"; R(D) = subsets of D↓×Can
  (Example 4.2(iii) with I = Can). → **A**.
- §6 Theorem 6.5 (induction): unary admissible predicates on D (Example 4.2(i), n=1). →
  within-a-domain, not a relation between two semantics.
- §6 Theorem 6.12 / Corollary 6.13 (co-induction): binary relations R ⊆ D × D on the **same**
  domain ("F-simulation"), concluding d ⊑ d′; includes applicative (bi)simulation. → **B**
  (homogeneous: D vs D, same semantics).
- Example 4.2(ii): n-ary non-strict relations on D × ⋯ × D. → B (homogeneous).
- The paper explicitly names the heterogeneous B case as an application of invariant
  relations but does **not** work it out: invariant relations "lie at the heart of some
  proofs of correspondence between denotational and operational semantics (as in (Plotkin,
  1985), or (Meyer and Cosmadakis, 1988, Appendix), for example), or between two denotational
  semantics (as in (Reynolds, 1974) for example)" (§2 Overview, under "Results — Invariant Relations",
  **p. 68** [V, the author's PDF at cl.cam.ac.uk/~amp12/papers/relpod/relpod.pdf, which carries the
  journal pagination: running head "68 ANDREW M. PITTS"]).

How it copes with recursive domains: minimal-invariant property (Freyd) + admissible actions
on relations; a mixed (negative/positive) separation R⁻/R⁺ and fixed-point induction.
Relation to our R: our R is a heterogeneous B relation (Clos4 finite approximations vs Clos3
denotations) in a graph model with no recursive domain equation at all (𝒫 Value is a
powerset of an inductive datatype); we instead face the same non-monotonicity in the *relation*
and resolve it by an index tower bounded by the finite side's depth — a "stage" method in
which the stages are tied to the finite element, combining the first two of Pitts's methods.

### B2. Pitts 1993/1994 MFPS, "Computational adequacy via 'mixed' inductive definitions"

```bibtex
@inproceedings{Pitts94MFPS,
  author    = {Andrew M. Pitts},
  title     = {Computational Adequacy via `Mixed' Inductive Definitions},
  booktitle = {Mathematical Foundations of Programming Semantics, 9th International
               Conference, New Orleans, LA, USA, April 1993, Proceedings},
  series    = {Lecture Notes in Computer Science},
  volume    = {802},
  pages     = {72--82},
  publisher = {Springer},
  year      = {1994},
  doi       = {10.1007/3-540-58027-1_3}}
```
**[V]** title, LNCS 802, pp. 72–82 (Pitts 1996 bibliography and the author PDF); DOI [U, from
search result].

Content **[V]**: untyped call-by-value functional language; formal-approximation relation
◁ ⊆ D × Prog (Definition 4), constructed by separating negative/positive occurrences,
simultaneous inductive definition of ◁⁻, ◁⁺, and proving them equal by fixed-point induction
using the minimal invariant (Theorem 6 "Existence of ◁"; Theorem 3 Computational Adequacy).
It repeats the three-method comparison (Milne/Plotkin/Reynolds stages; Martin-Löf via
information systems, "See [Winskel], Sect. 13.4"; and the new minimal-invariant method).
Abstract **[V]**: "proofs of correspondence between operational and denotational semantics
(or between two different denotational semantics) often depend upon the existence of
relations specified as the fixed point of non-monotonic operators."
§4 "Further development" **[V]**: "we believe that the recursively specified relation between
two recursively defined domains employed by Reynolds to relate a direct and a continuation
semantics of an untyped functional language in [12] can be constructed by applying our method
to a suitable binary relational structure." (Stated as a belief, not done.) It also notes the
minimal-invariant property amounts to "any element of a recursively defined domain ... can be
expressed as the least upper bound of a chain of projections of the element" [V].
Classification: the worked relation is **A**; the Reynolds remark is **B** (heterogeneous,
two domains), conjectural.

### B3. Reynolds 1974, "On the relation between direct and continuation semantics"
```bibtex
@inproceedings{Reynolds74,
  author    = {John C. Reynolds},
  title     = {On the Relation between Direct and Continuation Semantics},
  booktitle = {Automata, Languages and Programming, 2nd Colloquium (ICALP)},
  editor    = {Jacques Loeckx},
  series    = {Lecture Notes in Computer Science},
  volume    = {14},
  pages     = {141--156},
  publisher = {Springer},
  year      = {1974}}
```
The bibliographic data is **[V]** from Pitts 1996's bibliography. The content is **[V]**, read
from the CMU preprint (16 pages, KiltHub/figshare 6608018). The page numbers below are the
**preprint's own (1–16), not the LNCS pages**. The preprint says a preliminary draft was titled
"A Justification of Continuations".
- **Two different recursive domains [V].** The direct semantics uses "D ≅ P + (D → D)". The
  continuation semantics uses "C = E → O, D' = C → O, E ≅ P + (D' → D')" (pp. 2–3).
- **Relations [V].** η ∈ D ⇸ D' and θ ∈ (D→D) ⇸ (D'→D') (p. 4). θ has the logical clause
  "(∀a∈D, a'∈D') η: a↦a' implies η: f(a)↦f'(a')". The η clauses include "a = ⊥_D and
  (a' = ⊥_{D'}, or a' = λc∈C. error)". Theorem 1 (related environments give related meanings)
  is proved by structural induction.
- Theorem 2 (p. 6) also gives a retraction pair φ, ψ with "M[r](e) = ψ(N[r](φ·e))", "so that the
  semantics provided by M is included in the semantics provided by N" [V].
- **General construction [V]** (p. 14, "Relations between Recursively Defined Domains"): "We
  begin by defining θ_0 to be the universally true relation between the one-point domains D_0
  and D'_0 and θ_{n+1} = B(θ_n)". Then "θ_∞: x ↦ x' iff, for all n, θ_n: [x]_n ↦ [x']_n". This
  is an intersection over the stages via the projections, with uniqueness by induction on n
  (p. 15).
- Admissibility (p. 9) is "directed complete" relations: limits of related directed sequences
  are related.
- **Classification: B, heterogeneous (two different reflexive domains).** The relation's
  direction is D-to-D', but the construction is symmetric in form, since the converse of a
  directed complete relation is again directed complete (Cor. 3(3), p. 9) [V].
- **Indexing: stage-indexed.** Both sides are projected to stage n *in parallel*. Neither side
  is restricted to finite or compact elements.
- Mulmuley's assessment [V, CMU-CS-85-149]: "Though Reynolds' technique is very systematic, it
  can be used only when two domains have similar shapes or when one domain can be
  'transformed' into the other domain."
- **Relation to our R:** the closest *structural* precedent.
  - Same genre: a logical relation between two denotational semantics of a language,
    non-monotone because of the function clause, built as a tower θ_0 = ⊤, θ_{n+1} = B(θ_n).
  - Our tower R′ 0 = ⊤, R′ (suc k) = Obs (R′ k) has exactly the same shape.
  - The differences are three. (i) Reynolds indexes by the inverse-limit stage of *both*
    domains and intersects over all n. We index by the depth of the *finite target value* and
    show index irrelevance above the depth, so no limit or intersection is needed. (ii) We have
    no domain equation: 𝒫 Value is a powerset of an inductive type. (iii) Our relation is
    asymmetric: a finite approximation vs. an arbitrary set.

### B4. Inclusive predicates: Milne & Strachey 1976, Stoy 1977/1981, Mulmuley 1985/1987
- **Milne & Strachey**, *A Theory of Programming Language Semantics*, Chapman & Hall, 1976
  [U]. **Milne**, PhD thesis, Cambridge, 1973 [V, from Pitts's bibliography: "The formal
  semantics of computer languages and their implementations"].
- **Stoy**, *Denotational Semantics: The Scott–Strachey Approach to Programming Language
  Theory*, MIT Press, 1977 [U]. **Stoy**, "The congruence of two programming language
  definitions", TCS 13 (1981) 151–174, doi:10.1016/0304-3975(81)90037-2 [V bib via Crossref].
- **Stoy 1981, content [V, `related-denot/stoy-1981.pdf`, read 2026-10-15].** The PDF is a scan with a
  poor OCR layer; in the quotes below OCR misspellings are corrected, and nothing lost in the OCR is
  filled in. Page numbers are the printed TCS pages.
  - **What is related.** Not standard vs. store semantics (as these notes previously said, from
    secondary sources), but a denotational semantics and an interpreter for a small language PL:
    "one definition gave the denotational semantics, in the style of Scott and Strachey [12], and
    another defined the language using an interpreter, along lines similar to the use of VDL [6]. In
    this paper we present a proof of the congruence of these two definitions." (p. 151). PL is
    "simple enough for its semantics to be given solely in terms of environments" (p. 153).
  - **Two stages.** Stage 1 relates the direct semantics to a new continuation semantics (category
    B, same language); "Our first stage closely resembles this proof [Reynolds 1974], though our
    expression of it is a little different: Reynolds's use of 'directed complete relations'
    corresponds to our use of 'inclusive predicates'." (p. 152). Stage 2 relates the continuation
    semantics to the interpreter (category A: denotation vs. an operational definition), via
    "derepresentation functions, which map representations into the values they represent" (§8,
    p. 159).
  - **Existence (stage 1).** "These predicates have definitions which involve circularity and they
    can be rewritten as a fixed point equation. However, the function of which this set of predicates
    is the fixed point is not monotonic, and so the existence of such a fixed point cannot be inferred
    by the usual appeal to the result of Tarski" (p. 156). The construction: "The construction of
    solutions to these recursive domain equations involves sequences of 'approximation' domains, of
    which the required domains are, in some well-defined sense, the limits. We may define predicates
    on each of these approximation domains: this involves no circularity, but instead uses the
    predicates on earlier domains. Then we may define predicates for some element of the limit domain
    by applying the appropriate predicates to the element's images in all the approximation domains,
    and taking the conjunction of the results." (p. 156). So stage-indexed over both domains, then
    intersected, as in Reynolds.
  - **Asymmetry (stage 2 only).** Exact congruence predicates could not be shown to exist: "we must be
    content with predicates asserting that the denotational value is an approximation of the
    interpretive one" (p. 152); fixed-point induction on the interpreter gives only that "the
    interpreter defines a function which is weaker (in the sense of the partial ordering of the
    appropriate lattice) than that defined by the denotational semantics" (p. 158), so the proof
    goes in both directions and combines them (§11). The reason given: "The present extra
    complications arise in general when one tries to relate an infinitary abstract object, such as
    the function associated with some PL procedure by the denotational definition, with its finitary
    representation, such as the tree which represents the procedure in the interpreter." (p. 159);
    and, for the exact predicates, "Formally, it is the basis of the induction which fails" because
    the first approximation domain has one element "doing duty for all the functions" (§9.2, p. 163).
    Stoy leaves their existence open: "we are not thereby claiming that no such predicates exist (that
    is still an open question), but merely that we do not know how to demonstrate their existence"
    (p. 163).
  - Three inductions: "based on their size, their duration, and the richness of their value domains
    - and there is no correlation whatever between them." (p. 158). Interpreter functions are
    "represented by closures" (p. 167). Paper proof; mechanical aids are named as future relief
    (p. 169).
  - **For C6:** the stage indexing is by approximation domains of the inverse limit (not finite
    elements), and the order-asymmetric ("weaker than") predicates are between a denotation and an
    interpreter (category A), not between two denotations. Stoy's remark about an "infinitary
    abstract object" vs. its "finitary representation" names the same tension our relation handles,
    but on the operational side.
- **Content of the rest [V only via secondary sources]:**
  - Wand & Oliva (LFP 1992) [V]: "Such proofs typically involved complex arguments about
    inclusive predicates that related the domains in the source and target semantics [Milne &
    Strachey; Stoy] … by methods that were essentially denotational (induction on
    approximations to inverse limit domains)".
  - Mulmuley [V] on Stoy's example: an asymmetric predicate "Θ = {(d,e) | ∀(c,f) ∈ Π. dc ⊑
    O(e)f}" ("(d,e) ∈ Θ if d is weaker than e"). The existence proof "is shown using Milne's
    technique. The proof is undeniably complicated." The symmetric "=" version has no solution,
    shown by diagonalization with λx.xx.
- **Mulmuley**, "A Mechanizable Theory for Existence Proofs of Inclusive Predicates", CMU
  tech. rep. CMU-CS-85-149, 1985 [V, read]. Book: *Full Abstraction and Semantic Equivalence*,
  MIT Press (ACM Distinguished Dissertation), 1987 [U, not read]. CADE-7 1984 paper "The
  Mechanization of Existence Proofs of Recursive Predicates" [V as cited in the TR].
  - Setting [V]: two semantics ℰ1: L → D1 and ℰ2: L → D2. When a symmetric predicate does not
    exist, "a weaker predicate Q exists such that (d1,d2) ∈ Q iff d1 is weaker than d2", and
    equivalence is proved as two "weaker-than" directions.
  - Method [V]: work inside Scott's universal domain, representing domains as **finitary
    projections**. "L encapsulates the process of inverse limit construction of the domain D".
    Predicates live in a "predicate cpo".
  - Tool [V]: "IPL (Inclusive Predicate Logic) was implemented on top of LCF which can almost
    automatically prove the existence of most of the inclusive predicates which arise in
    practice."
  - Not indexed by finite elements [V].
- **Classification: B** (heterogeneous, two semantics), with stage/inverse-limit existence; Stoy
  1981's second stage is **A** (denotation vs. interpreter).
  Note the **asymmetric "weaker-than" predicates** (Stoy, Mulmuley): they are asymmetric in
  *order* (d ⊑-approximates e), not in finiteness, and in Stoy 1981 [V] they arise only in the
  denotation-vs-interpreter stage.
- **Polak 1980/81** [V, thesis STAN-CS-80-802 and the LNCS 124 book; see Part I
  §1.9]: a compiler proof whose code-generation relations ϑ between the LS (source) and LT
  (target) domains are recursive and, Polak notes, not even monotone ("If l increases ϑ_S becomes
  smaller", thesis p. 136, book p. 127). Existence is not proved: "Reynolds [Re74] presents a set
  of easy to check criteria that ensure existence of fixed points. It can be seen that our
  definitions satisfy his criteria; thus we subsequently assume that the above predicates are well
  defined." (§IV.5.3.5, thesis p. 136, book p. 127; identical wording in the book).
  Classification **B** (heterogeneous, compiler source vs target), first-order languages, not
  indexed by finite elements.
- **Relation to our R:** the historical home of "prove two semantics congruent by two one-way
  relations". Our two directions (preservation and reflection) echo this. Note that "finitary
  projection" is a technical term here (see Name check).

### B5. Meyer & Wand 1985; Filinski 1996/2007; Wand–Clinger single-model approach; Stoughton
- **Meyer & Wand**, "Continuation Semantics in Typed Lambda-Calculi (Summary)", *Logics of
  Programs*, LNCS 193, 1985, pp. 219–224 [V metadata via Crossref; V text, `related-denot/meyer-wand-1985.pdf`,
  read 2026-10-15; a six-page summary].
  - Abstract [V, p. 219]: "Previous work on the semantics of continuations has concentrated on
    untyped lambda-calculi and has used primarily the mechanism of inclusive predicates. Such
    predicates are easy to understand on atomic values, but they become obscure on functional
    values. In the case of the typed lambda-calculus, we show that such predicates can be replaced
    by retractions. The main theorem states that the meaning of a closed term is a retraction of
    the meaning of the corresponding continuationised term."
  - On the earlier line [V, p. 219]: Reynolds 74, Stoy 81 and Sethi & Tang 80 "all … discussed
    essentially an untyped lambda calculus with atoms, interpreted in Scott's D∞ model or something
    like it. … The key was the construction of a suitable relation. This was done by the method of
    inclusive predicates, which depended on the details of the models."
  - Method [V, pp. 219–223; page numbers inferred from the running heads, the first page being
    219]: simply typed λ-calculus with an answer type o; the CPS transform M ↦ M̄
    at type (α′ → o) → o, with (α → β)′ = α′ → (β′ → o) → o. Retractions α ◁ β are pairs of
    "lambda-definable maps i: α → β and j: β → α such that j ∘ i is the identity" (§6). Main
    Theorem (§9): for closed M of type α, M = j_α(J_α M̄) (OCR of the formula is damaged; the
    statement is that the direct meaning is recovered from the CPS meaning by a retraction).
    "Rather than have the direct and continuation meanings of a term connected by a relation, we
    show that the direct meaning may be recovered from the continuation meaning by a retraction …
    Hoare's notion of a 'concrete invariant' appears as a crucial part of the proof." (pp. 219–220).
    For open terms a type-indexed predicate P_α on representations (an "acceptable" predicate,
    §10) is needed; existence (§12): "We prove the existence of two acceptable predicates. The
    first uses induction on types; the second depends on the strong normalization theorem."
    "the reasoning in the proof lies entirely in the λ-calculus, and hence the theorem holds in
    any model" (p. 220).
  - Limits [V, §15, p. 223]: "The situation becomes more complicated if we study calculi in which
    strong normalization fails, such as the typed calculus with fixed-point operators. … it is not
    clear as of this writing whether this approach extends to these cases."
  - For C6: type-indexed, no recursion or fixed points, a retraction rather than a relation
    indexed by elements; not finite-element indexed.
  - Filinski's characterization [V, *Controlling Effects*, 1996, §3.4]: "Meyer and Wand's more
    abstract approach [MW85] applied to all models of simply-typed λ-calculi, but did not
    encompass computational effects – not even nontermination."
  - Classification B (term vs. its CPS transform, in models of the typed λ-calculus).
    Typed, so there are no reflexive domains.
- **Filinski**, *Controlling Effects*, PhD thesis, CMU, 1996 (CMU-CS-96-119 [U]). §3.4 [V]:
  "Early investigations [Rey74a, ST80, Sto81] were set in a domain-theoretic framework where
  the main difficulties concerned reflexive domains; as a result, these methods and results
  were closely tied to specific semantic models." Here ST80 = Sethi & Tang, JACM 1980 [U for
  details].
- **Filinski**, "On the relations between monadic semantics", TCS 375(1–3):41–75, 2007,
  doi:10.1016/j.tcs.2006.12.027 [V, full text `related-denot/filinski-2007.pdf`, read 2026-10-15]. The
  paper uses a metalanguage with general recursive types and multiple effects, and a "methodology
  for relating two such interpretations", with Reynolds's direct-vs-continuation example as the
  prototype.
  - **One object language, two semantics.** The goal is "comparing different denotational
    semantics of the same language" (§1, p. 41). The object language (Reynolds's untyped CBN/CBV
    λ-calculus with numerals) is translated once into the metalanguage: "Define a single,
    compositional translation of the sample language … to the metalanguage, in such a way that we
    can recover both the direct and the continuation semantics as particular domain-theoretic
    interpretations of effects in the metalanguage." (§1.5, p. 46). So it is not a compiler-like
    relation between two languages. Target theorem: "Theorem 1 (Agreement of Semantics). For closed
    t, [[t]]^D = Abs([[t]]^C)" (p. 45), where Abs identifies the error answer with divergence.
  - **Construction at recursive types: Pitts-style, by minimal invariance.** "Reynolds's paper goes
    back to the inverse-limit constructions of E^d and E^c, and reinforces them to construct the
    relation ≈ at the same time. In this paper we will use a more abstract method, due to Pitts,
    which establishes the existence (and uniqueness) of ≈ based only on a simple, equational
    characterization of minimality." (§1.4, p. 45). §3.3 "Relations on recursive types",
    Theorem 39 "(Existence of Invariant Relations)" (p. 65): for relational actions F_r^+, F_r^−
    "there exists a unique pair of admissible relations R^+, R^−" satisfying the fixed-point
    equations; existence by Knaster–Tarski on admissible relations ordered by ⊆ (positive) and ⊇
    (negative), uniqueness from minimal invariance ("Unlike Pitts's proof, ours does not exploit
    the fact that the Knaster–Tarski construction actually finds the least (pre)fixed point of the
    operator", p. 65). Example 40 (p. 66) shows uniqueness fails for a non-minimal solution.
  - **Indexing:** type-indexed over the metalanguage's types, including µ-types
    (r⟦µα.τ⟧θr), parameterized by relational actions for the effects (§3.2, §3.5). No
    stages, no step indices, no finite elements; symmetric (both sides are arbitrary elements of
    the two cpos).
  - Conclusion (§4, p. 73): "the naive, circular characterization of the logical relation at
    µ-types is actually uniquely satisfiable." Future work includes "relations … between syntax
    and semantics, as used to show agreement between a denotational semantics and an operational
    one".
  - Classification B, heterogeneous (two cpos), homogeneous in language. Does not affect C6.
- **Filinski & Støvring**, "Inductive reasoning about effectful data types", ICFP 2007 [V
  abstract]: "rigid induction" integrated into logical-relations arguments, used to show that
  success-stream and failure-continuation models of backtracking are equivalent. This is B
  (two models). The body was unread.
- **Wand–Clinger single-model approach** [V via Wand & Oliva 1992]: "Wand [18] showed how to
  avoid the use of inclusive predicates by modelling the target machine in the same semantic
  domains as the source semantics … refined by Clinger [3] to prove the correctness of a
  compiler for Scheme."
  - Wand & Oliva's own relations are on terms: "Since these are relations on terms (not their
    denotations), the existence of the relations is assured" [V].
  - Wand, "Correctness of procedure representations in higher-order assembly language", MFPS
    1991, LNCS 598 [V]. Closure representation is handled inside one λ-theory by a
    conservative-extension theorem (Theorem 3), not by a cross-model relation.
  - Clinger, "The Scheme 311 compiler: an exercise in denotational semantics", LFP 1984 [V,
    `related-denot/clinger-1984.pdf`; details in `vlisp-clinger-wand.md` §2]: target instructions get
    "a continuation semantics for each instruction" (p. 359) in the source's domains, and "Most of
    the correctness proof consists of trivial calculations. This is possible because the meanings
    of target code instructions are expressed in the same language used to express source
    meanings" (p. 356). Single model, so no inclusive predicates; the target keeps closures (a
    `lambda` instruction). Denotational in our sense (meanings are domain elements).
  - Classification: these *avoid* B by putting source and target in one model or theory. Wand
    1991 in particular is **not** a denotational semantics in our sense (author's classification,
    2026-10-15): meanings are λ-terms up to interconvertibility, which is not extensional, and no
    model is used except in the sketched conservativity proof. See `vlisp-clinger-wand.md` §3.
  - Relation to ours: our Clos3/Clos4 graph models are separate but similar. The single-model
    alternative is the obvious "why not just…" a referee may raise.
- **Stoughton** [V via the BRICS PCF bibliography]: Jung & Stoughton TLCA 1993 ("finitary PCF"
  fully abstract model), Stoughton "Mechanizing logical relations" MFPS 1993 (LNCS 802;
  definability in finite models), *Fully Abstract Models of Programming Languages* (Pitman
  1988). **No work relating two semantics over recursive domains was found**; the request may
  have meant Stoy.

### B6. Chlipala 2007 (denotation-to-denotation compiler proof) and closure-conversion proofs

#### B6a. Chlipala, PLDI 2007: the closest prior denotation-to-denotation compiler proof
```bibtex
@inproceedings{Chlipala07,
  author    = {Adam Chlipala},
  title     = {A Certified Type-Preserving Compiler from Lambda Calculus to Assembly
               Language},
  booktitle = {Proceedings of the ACM SIGPLAN 2007 Conference on Programming Language
               Design and Implementation (PLDI)},
  pages     = {54--65}, year = {2007},
  doi       = {10.1145/1250734.1250742}}
```
[V]. The source is the simply-typed λ-calculus with naturals and **no recursion**, so it is
total. "We first give each Source type a meaning by a recursive translation into sets" (Coq
types). The pipeline is Source → Linear → CPS → CC → Alloc → Flat → Asm. From Alloc on,
non-termination is modelled with co-inductive traces.
- Each pass is proved by a **logical relation between denotations of the source and target
  ILs, by recursion on types** [V]. On closure conversion [V]: "It relates denotations from the
  CPS and CC languages … f1 ≃_{τ⃗→N} f2 = ∀x1:[[τ⃗]]^P, ∀x2:[[τ⃗]]^C, x1 ≃τ⃗ x2 → f1 x1 ≃ f2 x2.
  This relation is almost identical to the most basic logical relation for simply-typed lambda
  calculus! The secret is that our meta language CIC 'has native support for closures.'"
- Chlipala's related-work claim [V]: "Semantics preservation proofs have been published before
  for individual phases … including closure conversion [MMH95]. All of these proofs that we are
  aware of use operational semantics."
- Classification **B**: heterogeneous (two ILs), symmetric, type-indexed, and total. There are
  no recursive domains, and no finite elements because the semantics is Coq functions.
- Relation to our R: this is the closest prior work in purpose (a closure-conversion-like pass
  proved by relating the denotations of source and target). Our setting differs in four ways:
  an untyped graph model with general recursion; a relation indexed by finite values, not
  types; asymmetric (finite approximation vs. arbitrary set); and reflection is the hard
  direction.

#### B6b. Chlipala, POPL 2010: operational
```bibtex
@inproceedings{Chlipala10,
  author    = {Adam Chlipala},
  title     = {A Verified Compiler for an Impure Functional Language},
  booktitle = {Proceedings of the 37th ACM SIGPLAN-SIGACT Symposium on Principles of
               Programming Languages (POPL)},
  pages     = {93--106}, year = {2010},
  doi       = {10.1145/1706299.1706312}}
```
[V]: "total correctness with respect to big-step operational semantics". The source is an
untyped mini-ML with fix, references and exceptions. The proof uses inductive compatibility
relations between source and target values, parameterised by closure heaps. Not
denotation-to-denotation.

#### B6c. Closure conversion elsewhere
- Minamide, Morrisett & Harper, "Typed Closure Conversion", POPL 1996, pp. 271–283,
  doi:10.1145/237721.237791 [V]. **Operational**: "a type-indexed family of logical relations
  relating closed source expressions to closed target expressions … defined by induction on
  source types".
- Wand & Steckler, "Selective and Lightweight Closure Conversion", POPL 1994, pp. 435–445,
  doi:10.1145/174675.178044. Journal version: Steckler & Wand, "Lightweight Closure
  Conversion", TOPLAS 19(1):48–86, 1997. Proof method **[V]**, journal version read
  (2026-10-16): operational (big-step evaluation and a labelled transition system), partial
  correctness, paper; see Part II §1. Not denotational.

### B7. Graph models (background for our model)
```bibtex
@article{Plotkin93,
  author  = {Gordon D. Plotkin},
  title   = {Set-Theoretical and Other Elementary Models of the $\lambda$-Calculus},
  journal = {Theoretical Computer Science},
  volume  = {121}, number = {1--2}, pages = {351--409}, year = {1993},
  doi     = {10.1016/0304-3975(93)90094-A},
  note    = {Part 1 reprints: A set theoretic definition of application, Memorandum
             MIP-R-95, School of Artificial Intelligence, Univ. Edinburgh, 1972}}
@article{Engeler81,
  author  = {Erwin Engeler},
  title   = {Algebras and Combinators},
  journal = {Algebra Universalis},
  volume  = {13}, number = {1}, pages = {389--392}, year = {1981},
  doi     = {10.1007/BF02483849}}
@article{Scott76,
  author  = {Dana Scott},
  title   = {Data Types as Lattices},
  journal = {SIAM Journal on Computing},
  volume  = {5}, number = {3}, pages = {522--587}, year = {1976},
  doi     = {10.1137/0205037}}
```
All [V] via Crossref. Memo number [V] from the reference list of the Edinburgh preprint.
- Plotkin 1972/1993 [V, preface of the preprint]: "an elementary set-theoretical model of the
  λβ-calculus. Functions are modelled … by their graphs". Application is
  x·y = ⋃{ν | ∃ finite µ ⊆ y. µ→ν ∈ x}.
- Engeler 1981 [U: description via Plotkin and Siek 2017, not Engeler's text]: model P(B_A)
  with B_A = A ∪ (P_f(B_A) × B_A); application x·y = {b | ∃ finite µ ⊆ y. (µ,b) ∈ x}. It was
  used for combinatory logic.
- Scott 1976 [U: description via Plotkin]: the graph model Pω, with x·y = {m | ∃ e_n ⊆ y.
  (n,m) ∈ x}.
- Siek 2017 §2.1 [V] gives P(D_P) with D_P = Z + P_f(D_P) × P_f(D_P) and P(D_E) with
  D_E = Z + P_f(D_E) × D_E, adapted to CBV.

Our model is Engeler/Plotkin style: arbitrary sets of finite values, with no consistency or
entailment closure.


---------------------------------------------------------------------------------------------

## Synthesis
### S1. Lineage of the ideas

**(a) Finite-element / token recursion (category A throughout).**
- Martin-Löf 1983 [V] relates a formal neighbourhood (a syntactic finite element) to a program,
  inductively on the neighbourhood's syntax; the untyped, reflexive setting is no obstacle.
- The method passes through Plotkin's lecture notes [U which ones] and is used by Abramsky's
  domain logic (formulas, LLC 1990 §5) [V].
- Winskel 1993 §13.4, Lemma 13.7 [V] states it for information-system tokens, by well-founded
  recursion on token size.
- Pitts 1993/1996 [V] names it "essentially due to Martin-Löf" and grounds it in the fact that
  {d | d ◁ e} is Scott-closed, so the relation on compact elements determines it.
- Intersection-type realizability (Krivine ch. 3, Lemma 3.5 [V]) is the same idea with types
  as the finite syntax.
- Siek 2017 §5.1 ("element-indexed" G) [V] and PLFA Adequacy (𝕍/𝔼 by recursion on Value) [V]
  are the graph-model versions.
- **All of these relate finite elements to syntax or operations, never to a second
  denotation.**

**(b) Stage / step indexing.**
- Milne 1973, Plotkin 1973 and Reynolds 1974 [V for Reynolds] build relations as towers θ_0 =
  ⊤, θ_{n+1} = B(θ_n) over the inverse-limit stages of *both* domains, then intersect over n.
  Stoy 1981 [V] ("approximation domains … taking the conjunction of the results", p. 156) and,
  per secondary sources, Milne–Strachey and Mulmuley use the same inverse-limit route for
  inclusive predicates.
- Pitts 1993/1996 [V] replaces stages by the minimal-invariant property (mixed fixed points).
  BKV 2009 mechanizes that route [V].
- Operational step-indexing appears in Benton–Hur 2009 [V], on the machine side only, with an
  admissible closure in the other direction, and in Hur–Dreyer 2011 [V] (both sides
  operational).
- Our tower has the same shape as Reynolds's. The index is the depth of the finite target
  value, and index irrelevance above the depth removes the need for limits or intersections.

**(c) Denotation-to-denotation relations (category B).**
- Reynolds 1974 [V]: direct vs. continuation; two different reflexive domains; stage-indexed.
- Milne–Strachey 1976 [U primary, V secondary]: inclusive predicates; inverse-limit induction.
- Stoy 1981 [V]: direct vs. continuation semantics of one language (B, symmetric congruence
  predicates, built on approximation domains and intersected), then continuation semantics vs. an
  interpreter (A, order-asymmetric). Not standard vs. store semantics, as these notes had said.
- Mulmuley 1985/87 [V TR]: a general mechanized existence theory for two semantics (D1, D2),
  via finitary projections in a universal domain; asymmetric "weaker-than" predicates.
- Meyer–Wand 1985 [V]: typed λ-calculus without fixed points; the direct meaning of a closed term
  is recovered from the meaning of its CPS transform by a λ-definable retraction; a type-indexed
  "concrete invariant" for open terms.
- Pitts 1996 §6 [V]: homogeneous binary relations on one domain (simulations / co-induction).
  Pitts 1993 §4 [V] only conjectures that Reynolds's heterogeneous relation fits his method.
- Filinski 2007 [V]: two monadic interpretations of one metalanguage (hence of one object
  language), related by a type-indexed logical relation; at µ-types the relation exists and is
  unique by a Pitts-style argument (Theorem 39, p. 65: Knaster–Tarski plus minimal invariance).
  Symmetric, no stages, no finite elements.
- Chlipala 2007 [V]: pass-by-pass relations between the denotations (Coq sets) of source and
  target ILs, including closure conversion. Type-indexed, total source, no recursive domains.
- Polak 1980 [V]: heterogeneous source/target predicates for a first-order Pascal-subset compiler;
  existence assumed via Reynolds's criteria.
- The Wand–Clinger line [V via Wand–Oliva] avoids B by using one model (Clinger) or one equational
  λ-theory (Wand 1991, not denotational in our sense) for source and target.

**(d) Asymmetry.**
- Finite-vs-arbitrary asymmetry exists only in category A: a finite token, neighbourhood,
  type, formula or Value against a term or closure (Martin-Löf, Winskel, Abramsky,
  Siek/PLFA).
- Benton–Hur 2009 [V] is asymmetric in a different sense: half-denotational, half-operational,
  with step indices on the machine side only.
- Stoy/Mulmuley use order-asymmetric "weaker-than" predicates, but over whole domains. In Stoy
  1981 [V] they relate a denotation to an interpreter (category A), and Stoy explains the need for
  them by the gap between "an infinitary abstract object" and "its finitary representation, such
  as the tree which represents the procedure in the interpreter" (p. 159).

### S2. Answers for Part B specifically
- **Is any prior denotation-to-denotation relation indexed by finite elements?** None that we
  found or verified.
  - Reynolds/Milne/Stoy/Mulmuley index by inverse-limit stages of both domains, which are
    projections of arbitrary elements, not compact elements.
  - Pitts uses the minimal invariant, and so does Filinski 2007 [V] for relations between two
    monadic interpretations.
  - Chlipala, Meyer–Wand [V] and Filinski [V] use types (Filinski's types include µ-types).
  - The finite-element method (Martin-Löf/Winskel) appears in the literature only for adequacy
    (category A). Pitts describes it only in that role, and it is restricted to Scott domains
    via information systems.
  - Caveats: the primary texts of Milne–Strachey and Mulmuley's book are unverified. (Filinski
    2007 and Stoy 1981 are now read; neither indexes by finite elements.)
- **Is any prior B relation asymmetric with a finite element on one side and an arbitrary
  element on the other?** None found.
  - The only asymmetric relations seen between semantics are order-asymmetric (Stoy/Mulmuley
    "weaker-than", Reynolds's η direction), not finiteness-asymmetric; Stoy's [V] are between a
    denotation and an interpreter, so they are not even B.
  - **Safe phrasing for the paper:** "to our knowledge, the first relation between two
    denotational semantics indexed by a finite approximation on one side". Keep "to our
    knowledge" because of the gaps above.
- **Purpose match.** The only prior denotation-to-denotation proof of a closure-conversion-like
  pass that we found is Chlipala 2007, which is typed, total and type-indexed. Wand MFPS 1991
  treats closure representations inside one λ-theory.

### S3. Claims that remain unverified (do not state without checking)
Resolved on 2026-10-15: Pitts 1996's issue number (2) and the page of the §2 Reynolds remark
(p. 68); the Krivine English edition (Ellis Horwood 1993, from Open Library, translator unverified).
Resolved in the third pass (PDFs in `related-denot/`): Filinski 2007 (construction:
§3.3, Theorem 39), Meyer–Wand 1985 (content), Clinger 1984 (content), Stoy 1981 (content; it
corrects the earlier "standard vs. store" description), Abramsky & Ong 1993 (image-only scan read
page by page: adequacy via the domain logic, Theorem 5.4.9, p. 206; see A4b). None of the items below
bears on C3; items 5–6 are the remaining caveats on C6.

1. Which "Gordon Plotkin's lecture notes" Winskel means in §13.11 (Pisa notes [80] or CSLI 1985
   [83]).
2. Winskel chapter numbering in later printings (a 2001 listing appears to differ).
3. Whether the DTLF APAL article contains the lazy-λ adequacy material. (Abramsky & Ong 1993's
   adequacy method: resolved, see A4b.)
4. Krivine English edition: translator and series.
5. Milne–Strachey 1976 and Stoy 1977 (the book): chapter and section locations of the
   inclusive-predicate constructions.
6. Mulmuley's 1987 book (only the 1985 TR was read).
7. ~~Wand–Steckler 1994 proof method~~ (resolved 2026-10-16: operational, from the TOPLAS 1997 version).
8. Sieber 1992 bib and whether it uses "finitary". Whether the O'Hearn–Riecke body (not just
   the abstract) uses "finitary logical relations".
9. Engeler 1981 and Scott 1976 one-line descriptions (taken from Plotkin and Siek, not the
   originals).
10. The BBKV "Formalizing Domains…" final publication venue.
11. Name check: no Google Scholar, DBLP or ACM full-text search was completed (still blocked on
    2026-10-15: Scholar 429, DBLP bot check, ACM 403). OpenAlex and arXiv abstract searches for
    the novelty claims found no relation between two denotations indexed by finite elements.
