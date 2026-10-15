# Novelty check: mechanized compiler correctness with denotational (graph-model) semantics

Compiled 2026-10-15. Read-only literature search.

## How each claim was checked

- **[V]** Verified in this session from the primary source (PDF text or the author's own page). Quotes are verbatim.
- **[V-notes]** Verified in the repo's earlier notes. These are `papers/PLDI-2027/notes/related-work-literature.md` at commit f989398 and `related-work-closure-conversion.md` on mu-main. Both marked the item as read from the primary source. I did not re-read it this session.
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
- **BahrHutton22 [V, Zenodo README].**
  - Agda; `Lambda.agda` is a "Call-by-value lambda calculus (section 3)".
  - The semantics is an evaluator into the coinductive partiality monad, using sized types.
  - The README says: "the termination checker is disabled for `exec` (using the `TERMINATING` pragma) and termination is proved manually".
  - The source semantics is a monadic definitional interpreter (environment and closure values), not a graph model.
  - The target is a VM. Single pass (calculated). No closure conversion [M: inferred from the single-VM design; check §3].
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

- **Œuf [A].**
  - A verified compiler from a Gallina subset to assembly, built on CompCert.
  - The source is related to Gallina by a "computational denotation" into Coq functions. The source is total.
  - Closure conversion appears inside the compiler, but the passes are proved operationally [M].
- **Cogent [A].**
  - A certifying compiler for a total, linearly typed language.
  - The proof is that the generated C refines an Isabelle/HOL shallow embedding, i.e. a denotation into HOL functions.
  - No general recursion. Proofs are per program.
- **McKinna & Wright [A].** "A type-correct, stack-safe, provably correct expression compiler in Epigram". The JFP submission was dated 2006; the final publication is [M]. Arithmetic expressions only, total.
- **Pardo, Gunther, Pagano & Viera, "An Internalist Approach to Correct-by-Construction Compilers", PPDP 2018 [A, title and authors only].** The proof assistant and the kind of semantics are **unverified**.
- **Compared with ours:** in all of these the denotation is the meta-language's own function space, and the source is total.

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
- **Polak81 [A metadata only].** I recall it as a Pascal-subset compiler proof based on denotational semantics, with parts checked by the Stanford Pascal Verifier. **This is UNVERIFIED and matters:** if true, it is the earliest machine-assisted denotational compiler proof. Check the book's introduction before writing "first mechanized … denotational".
- **Clinger84 [A, secondary annotation].** Continuation semantics of Scheme, factored into combinators that are VM primitives, with sketched correctness proofs.
- **Wand91 [A, plus V-notes].** Closure and procedure representations are handled inside a single λ-theory by a conservative-extension theorem. On paper. **Classification (author, 2026-10-15): not denotational.** Meanings are λ-terms up to convertibility, which is not extensional, and there is no model (only the sketched conservativity proof uses the open term model). Describe it as a compositional translation into an equational λ-theory (the Wand–Clinger single-theory approach). See `vlisp-clinger-wand.md` §3. Wand's index page [V] describes the paper's own summary as "proves a compiler from a tiny language into HOAL correct".
- **WandOliva92 [V-notes].** "relations on terms (not their denotations)". The Wand–Clinger "single model" approach models the target machine in the same domains as the source.
- **VLISP95 [A, plus Benton–Hur's characterisation V].**
  - Scheme to byte code, based on the Clinger–Rees denotational semantics. Untyped, with recursion and closures.
  - "the proofs were not mechanized" (Benton & Hur 2009).
  - A MITRE report, "The Faithfulness of the VLISP Operational Semantics" (1992), relates the byte-code operational semantics to its denotational semantics [A, title only]. This is the nearest **paper** precedent for target-side adequacy.
- **Palsberg92 [A metadata only].** Compiler generation from action semantics. Paper proof.
- **Compared with ours:** these are the conceptual ancestors (denotational compiler correctness, closure representations, and a denotation-to-machine faithfulness proof). None is mechanized, except possibly Polak (unverified), and none uses a graph model.

### 1.10 Operational contrast (one line each)

All of these are [A] or [V-notes]; the details are in `related-work-closure-conversion.md`.

- **CompCert, CompCertO, CompCertTSO:** operational simulations.
- **CakeML:** functional big-step semantics with clocks.
- **CertiCoq (Paraskevopoulou & Appel, ICFP 2019; Paraskevopoulou, Li & Appel, ICFP 2021):** step-indexed logical relations, untyped closure conversion.
- **Pilsner (ICFP 2015):** parametric inter-language simulations.
- **Chlipala, POPL 2010:** big-step semantics, terminating programs only.
- **Wang & Nadathur, ESOP 2016:** Abella.
- **Pyrosome (OOPSLA 2025):** equational theories.
- **Minamide, Morrisett & Harper (POPL 1996), and Ahmed & Blume (ICFP 2008):** operational, typed closure conversion.

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

- **Siek17 (arXiv, v4 21 Oct 2017) [A abstract; V-notes for §5–6].**
  - A graph model for CBV λ ("functions … as finite graphs").
  - The abstract claims "the first machine-checked proof that such a model is sound and complete with respect to an operational semantics" (paraphrased by the fetch tool; check the exact wording).
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
- **MossesCockxReus26 [A].** Scott–Strachey denotational definitions embedded in Agda with postulated domain constructors: an untyped λ model, PCF, and a Scheme sublanguage. No compiler, and not `--safe`-style.
  - A related artifact is Mosses, "Shallow Agda embedding of denotational semantics in article 'Checking a denotational semantics of Scheme in Agda'", 2025, doi:10.1145/3747410 [A, Crossref].
- **Domain-theoretic, not graph models:**
  - de Jong & Escardó, Scott's D∞ in Agda/TypeTopology [V-notes abstract].
  - BKV09 in Coq [V-notes].
  - Garlene, guarded recursion in Lean, arXiv 2609.24345 [A]: it re-proves adequacy for a λ-calculus with fixpoints and says the results are not new.
- **Intersection-type mechanizations without models used for compilation:**
  - Laurent's Coq proof of BCD transitivity [A, via Siek19].
  - Larchey-Wendling's constructive λ-calculus in Coq, with intersection systems D and DΩ [A].
- **Not found:** any Coq, Lean or Agda development using a graph or filter model as the semantics of a compiler between *different* languages, apart from this project.
- **Verdict for (2):** the only mechanized uses of graph or filter models for program transformations that I found are Siek's own: the Isabelle inliner (2017) and the AFP entry. Both are same-language.

---

## (3) Mechanized adequacy of a denotational semantics for a low-level / assembly target

- **Chlipala07 [V].** Asm gets a trace denotation, but there is no separate machine semantics and no adequacy theorem. The denotation is the definition.
- **XiaITrees20 [V].** Asm gets an ITree denotation. The ITrees are executable by extraction, but there is no adequacy theorem against a separately defined machine. The paper contrasts itself "with non-executable models based on small-step operational semantics".
- **Kan & Ertel 2026 and Vellvm [A].** ITree semantics for RISC-V and LLVM IR. Validated by test suites; no adequacy against an independent machine was seen.
- **Benton & Hur 2009 [V].** Relates a *source* denotation to machine behaviour. Lemmas 5 and 6 are named "Adequacy for bottom" and "Ground termination adequacy". The low-level side has no denotation, so this is the inverse of our setting.
- **RockSalt / bigrammar decoder DSL (Coq) [A].** Denotational and operational semantics of an x86 *decoder* DSL, with adequacy between them. Not program execution.
- **VLISP [A, title only].** "Faithfulness" of a byte-code operational semantics to its denotational semantics. On paper.
- **Verdict for (3):** I found no mechanized adequacy proof of a denotational semantics (of any kind, let alone a graph model) for an assembly-level language against an abstract machine. The nearest are VLISP (paper, byte code) and the Coq decoder DSL (not execution).

---

## Synthesis: candidate novelty claims

| # | Candidate claim | Verdict | Safe phrasing |
|---|---|---|---|
| C1 | "First mechanized compiler-correctness proof using denotational semantics" | **Contradicted** by Chlipala07 (Coq, every intermediate language), Benton–Hur 2009 (source), XiaITrees20 (Imp/Asm), Cheng et al. 2026 (CompCert front end). Polak 1981 may also predate it (unverified). | Do not claim. Cite these four works as the denotational line. |
| C2 | "First verified compiler whose correctness is proved with graph-model semantics" | **Supported, to our knowledge.** The only prior mechanized graph-model transformation proof is Siek's 2017 inliner (same language). PLFA has none. | "To our knowledge, this is the first verified multi-pass compiler, beyond same-language optimizations [Siek 2017], whose correctness is stated and proved using graph-model (Plotkin/Engeler-style) denotational semantics for every intermediate language." |
| C3 | "First denotational proof of closure conversion" | **Contradicted as stated** (Chlipala07 CPS→CC). Wand91 handles procedure representations on paper in an equational λ-theory, which is not a denotational semantics (see the entry above), so it is related work but not a counterexample. **Qualified version supported:** first for a source with general recursion and divergence (and recursive types, plus an untyped variant), denotation to denotation, mechanized. | "Unlike Chlipala's typed, total source, ours has general recursion through iso-recursive types; to our knowledge this is the first mechanized denotation-to-denotation proof of closure conversion for such a language." |
| C4 | "First mechanized denotational correctness proof of a compiler from a higher-order language with general recursion to assembly" | **Qualified.** Benton–Hur 2009 is mechanized, with recursion, but compiles to an SECD machine with closures (one pass, no closure conversion, operational target). VLISP is untyped Scheme to byte code but on paper. Chlipala07 is total. | "…the first mechanized compiler from a higher-order language with general recursion to an assembly language in which every pass, including closure conversion, is proved using denotational semantics." Keep "to our knowledge". |
| C5 | "Per-pass correctness is equality of denotations, ⟦src⟧ ≃ ⟦tgt⟧" | **Qualified, as a distinguishing feature, not a priority claim.** Chlipala uses type-indexed logical relations; Benton–Hur uses realizability. The Wand–Clinger single-model approach also equates meanings in one model (on paper). | "For most passes, correctness is literally equality of graph-model denotations; only closure lowering needs a relation." |
| C6 | "New approximant logical relation between two graph-model denotations" | **Supported, to our knowledge** (per the prior notes, Part B: no denotation-to-denotation relation indexed by finite elements was found). Gaps: Filinski 2007's construction and the primary texts of Milne–Strachey, Stoy and Mulmuley are unread. | "To our knowledge, the first relation between two denotational semantics indexed by a finite approximation on one side." |
| C7 | "First mechanized adequacy of a graph model (or of any denotational semantics) for an assembly language against an abstract machine" | **Supported, to our knowledge.** Chlipala and ITrees give assembly denotations without machine adequacy. VLISP's byte-code faithfulness is on paper. | "To our knowledge, the first mechanized adequacy proof for a denotational (graph-model) semantics of an assembly-level language." |
| C8 | "End-to-end: source and compiled x86 both stop with the same constant or both diverge, via denotations plus adequacy at both ends" | **Qualified.** Benton–Hur proves both directions for SECD; ITrees gives termination-sensitive bisimulation (Imp/Asm); Chlipala gives termination for a total source. New in combination: higher-order with recursion, closure conversion, assembly, adequacy at both ends. | State the theorem and compare; avoid "first end-to-end". |
| C9 | "Same compiler also proved in three operational styles; controlled comparison" | **Supported, to our knowledge, for denotational versus operational.** Leroy & Grall (2009) and Danielsson (2012) are precedents for different *operational* styles on one (one-pass) compiler. | "To our knowledge, the first side-by-side mechanization of one multi-pass compiler in a denotational style and in three operational styles." |
| C10 | "Agda `--safe`, standard library only, no postulates" | **Engineering claim, qualified.** BahrHutton22 uses sized types and `TERMINATING` pragmas, with termination proved separately [V README]. Danielsson12 uses workarounds for productivity [V]. MossesCockxReus26 postulates domain constructors [A]. Whether sized types are rejected by `--safe` in current Agda is [M]. | "Fully `--safe` Agda: no postulates, no termination or productivity pragmas, no coinduction." |

### Remaining unverified gaps (check before submission)

1. **Polak 1981.** Is the proof denotational, and was it mechanically checked (Stanford Pascal Verifier)? This affects how C1 is worded; it does not threaten C2–C9.
2. **VLISP.** The content of "The Faithfulness of the VLISP Operational Semantics" (MITRE M92B093, 1992). Also how VLISP handles closures. Read Guttman, Ramsdell & Swarup, "The VLISP verified Scheme system", LASC 8(1/2):33–110.
3. **BahrHutton22 §3.** Confirm that the target VM has primitive closures, i.e. no closure conversion.
4. **Œuf.** Confirm whether any passes are proved denotationally.
5. **Pardo et al., PPDP 2018.** Semantics style and proof assistant.
6. **Siek's OlivierFest 2025 "Verified Nanopasses for Compiling Conditionals".** Agda, four passes to an x86-like language [A]. Which semantics? If graph-model, cite it as a precursor, in the third person.
7. **Siek17 wording.** Check the exact wording of the "first machine-checked" sentence in the arXiv abstract before quoting.
8. **Mosses, Cockx & Reus 2026, and Mosses 2025 (Scheme in Agda).** Confirm there is no compiler.
9. **Not checked: game semantics.** Ghica's Geometry of Synthesis (paper, not mechanized [M]) and CompCertO (operational, "game-semantics-inspired" [M]). Expected to be contrast only.
10. **Not checked: "Kavvos".** No relevant compiler-correctness paper found; dropped.
11. **Not checked: Hutton & Wright, "Compiling exceptions correctly", and other paper-only calculational works.** Mention generically.
12. **No DBLP or Scholar search was completed** (rate-limited). A final full-text sweep for "graph model" + "compiler" and for "filter model" + "compiler correctness" would close C2 and C7.
