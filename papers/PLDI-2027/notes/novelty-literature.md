# Novelty check: mechanized compiler correctness with denotational (graph-model) semantics

Compiled 2026-10-15. Read-only literature search. A second pass the same day closed most of the gaps listed at the end (Polak 1980/81, the VLISP faithfulness report, Bahr–Hutton 2022, Œuf, Pardo et al., Siek 2025, Siek 2017's wording, Mosses 2025/2026, game semantics) and ran the final searches; the entries below record what was found and where.

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
- **BahrHutton22 [V, Zenodo README].**
  - Agda; `Lambda.agda` is a "Call-by-value lambda calculus (section 3)".
  - The semantics is an evaluator into the coinductive partiality monad, using sized types.
  - The README says: "the termination checker is disabled for `exec` (using the `TERMINATING` pragma) and termination is proved manually".
  - The source semantics is a monadic definitional interpreter (environment and closure values), not a graph model.
  - The target is a VM. Single pass (calculated). **No closure conversion [V, artifact `agda/Lambda.agda`, the file the README assigns to §3]:** the VM has closure values and a closure-building instruction, `Clo' : Code → Env' → Value'`, with `exec (ABS c' c) (s , e) = exec c (VAL (Clo' c' e) ∷ s , e)` and `exec (APP c) (VAL v ∷ VAL (Clo' c' e') ∷ s , e) = later (∞exec c' (CLO c e ∷ s , v ∷ e'))`; the compiler clause is `comp (Abs x) c = ABS (comp x RET) c`. The paper text itself was not obtained (ACM and the Nottingham repository returned bot checks), so this is checked against the published artifact (Zenodo 10.5281/zenodo.6794696), not §3's prose.
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
- **Pardo, Gunther, Pagano & Viera, "An Internalist Approach to Correct-by-Construction Compilers", PPDP 2018, pp. 1–12, doi:10.1145/3236950.3236965 [Crossref metadata; abstract A via OpenAlex; paper body not obtained (ACM 403, OpenAlex marks it closed)].**
  - Abstract: "a methodology to organize the construction of a correct compiler, taking advantage of the power of full dependently type systems. The basic idea consists in decorating the abstract syntax of languages with their semantics, allowing to express the correctness of the compiler at type level … a correct-by-construction compiler from an imperative language with conditional iteration to a stack based intermediate language … combined with the externalist approach, compiling from the intermediate language to an assembly-like low level code and separately proving its correctness."
  - **Agda [V, the authors' 2016 talk slides "An Approach to Correct-by-Construction Compilers", Montevideo 2016]:** "Our development is in the context of dependently typed programming, using Agda." In the slides the semantics is a compositional "semantic algebra" (functions in Agda); the While case uses a clock: "fwhile fb fc zero σ = nothing; fwhile fb fc (suc clock) σ = …". The stack machine also gets a big-step relation ⟨c, s⟩ ⇓M s′. Whether the 2018 paper keeps exactly this is unverified.
  - First-order, imperative (While), no closures. Contrast only.
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
- **Polak81 [V, from the thesis it revises].** Read: W. Polak, *Theory of Compiler Specification and Verification*, PhD thesis, Stanford, 1980, report STAN-CS-80-802 (DTIC AD-A094604, scan on the Internet Archive as `DTIC_ADA094604`; pages read as images, thesis page numbers). The LNCS 124 book is described as "a revised version of my Ph.D. thesis" [A, CiNii record]; the book itself was not seen.
  - **Denotational, yes.** Source and target are both given Scott–Strachey continuation semantics: "the source language by specifying a function smean mapping character strings into their meaning" (§I.3.4, p. 17); for the target "we use denotational semantics for this purpose" (§I.3.3, p. 17); §III.2.2 is "Denotational semantics" and §III.2.2.3 "Denotational definition of a machine language" ("Continuations in the target language are mappings of the form D → S → M → A", p. 62). The logic is Scott's LCF (§II.2, "Scott's logic of computable functions").
  - **Correctness statement:** a commuting square with smean, tmean and the identity, read as partial correctness: "the correct statement is 'given that our compiler terminates then the above diagram commutes'" (§I.4.1, p. 18); for the code generator, "exit tmean(out) = dsem(in)" (p. 19).
  - **Machine-checked, in part.** Abstract (p. iii): "The Stanford verifier is used to give a complete formal machine checked verification of the compiler." But §I.5.2 (p. 27): "Although the development of a suitable logical basis for our compiler verification is done manually all actual program proofs are completely machine checked." The compiler is a Pascal Plus program verified with the Stanford Pascal Verifier against its specifications; the theory those specifications rest on (lemmas about the semantics) was developed by hand. The relations between source and target domains (§IV.5.3.4, ϑ predicates) are recursive and non-monotone; their existence is not proved but assumed by appeal to Reynolds 1974: "To repeat the theory of 'inclusive' predicate is beyond the scope of this thesis. However, Reynolds [Re74] presents a set of easy to check criteria that ensure existence of fixed points. It can be seen that our definitions satisfy his criteria; thus we subsequently assume that the above predicates are well defined." (§IV.5.3.5, p. 136).
  - **Languages:** LS, a Pascal subset with recursive procedures and functions, jumps, arrays, records and pointers (abstract, p. iii); **first-order**: "Procedures and functions may not be passed as parameters" (§III.1.2, p. 57). Target LT: "assumes a stack machine including a display mechanism [RR64, Or73] to handle procedure and function calls" (p. 2), a hypothetical machine (§III.7). No closures, no closure conversion; the compiler is scanner, parser, static semantics and a single code generator (§I.4.1, p. 19).
  - **Effect on our claims:** it is an early (1980) machine-checked compiler proof stated with denotational semantics, so it is another reason not to claim C1. It does not touch C2–C9: first-order source, no recursive types, no closure conversion, a hypothetical stack machine whose meaning is its denotation (no adequacy), and the semantic theory itself is not mechanized.
- **Earlier mechanized work cited by Polak [V that Polak says this; primary texts not read].** §I.5.1 (pp. 25–26): "The same proof method is used by Milner and Weyhrauch [MW72, WM72] in 1972 to verify a compiler for an algolic language. But they introduce yet another innovation: semantics and proof are described in Scott's logic of computable functions"; "Avra Cohn [Co79a, Co79b] proves the correctness of several components of a compiling algorithm using the Edinburgh implementation of LCF". Also "A machine checked proof of the McCarthy/Painter compiler has been done by W. Diffie but has not been published." (p. 25). Milner & Weyhrauch, "Proving compiler correctness in a mechanized logic", Machine Intelligence 7, 1972 [M for the venue details]. These are first-order (algolic) and predate Polak; again only relevant to C1.
- **Martin & Toal, "Case Studies in Compiler Correctness Using HOL", International Workshop on the HOL Theorem Proving System and Its Applications, 1991, pp. 242–252, doi:10.1109/HOL.1991.596291 [Crossref metadata; abstract A via OpenAlex].** "In the first case study, the source and target language semantics are direct denotational, and the compiler correctness proof is done by structural induction supplemented by computation induction where necessary. In the second case study, the source and target languages are given a structural operational semantics". Source "a sample imperative sequential language", target "abstract, stack-based, and executes tree-structured code". The abstract describes one source language and one target machine for both studies; whether it is literally the same compiler proved twice is unverified (body not read). If it is, it is an early instance of **one compiler proved both denotationally and operationally in a proof assistant** (relevant to C9): a toy imperative language, one pass, first-order, so C9's "multi-pass" and "three operational styles" still separate ours.
- **Clinger84 [A, secondary annotation].** Continuation semantics of Scheme, factored into combinators that are VM primitives, with sketched correctness proofs.
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
- **Compared with ours:** these are the conceptual ancestors (denotational compiler correctness, closure representations, and a denotation-to-machine faithfulness proof). Polak's program proofs are machine-checked (the semantic theory is not), and the LCF work of Milner–Weyhrauch and Cohn is mechanized (per Polak); all of these are first-order. The higher-order ones (Clinger, Wand, VLISP) are on paper. None uses a graph model.

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
- **VLISP [V, M92B093; see §1.9].** Faithfulness of the tbc byte-code machine to its denotational semantics: one direction (machine answer ⇒ same denotation), on paper, byte code with primitive closures.
- **Tune & Kavvos, "Bimodels and Biorthogonality for Abstract Machines", ICFP 2026 [A, the Zenodo artifact description only, doi:10.5281/zenodo.20507720].** "a complete Agda 2.8.0 / agda-stdlib 2.3 mechanization of the paper's results: the CK and CEK abstract machines, their bimodels, the biorthogonality-based logical relations, and results relating the two machines." Mechanized semantics for abstract machines (CK/CEK, not assembly); whether it includes an adequacy theorem of a denotational model is not stated there. Adjacent to C7, not a counterexample on what was seen; read the paper if C7 is stated broadly ("abstract machine" rather than "assembly language").
- **Verdict for (3):** I found no mechanized adequacy proof of a denotational semantics (of any kind, let alone a graph model) for an assembly-level language against an abstract machine. The nearest are VLISP (paper, byte code, one direction) and the Coq decoder DSL (not execution).

---

## (4) Game semantics (contrast, one line each)

- **Ghica, "Geometry of Synthesis", POPL 2007, doi:10.1145/1190216.1190269 [A, abstract via OpenAlex].** Hardware synthesis from an SCI-typed higher-order language using "a semantic model inspired by game semantics and the geometry of interaction … A soundness result is given, which is also a correctness result for the compilation technique." A semantics-directed compiler to circuits with a paper soundness proof; no mechanization seen (GoS IV, ICFP 2011, doi:10.1145/2034773.2034805 [A], extends it to affine recursion and benchmarks it; no mechanization mentioned). Not a counterexample: target is hardware, the model is game/GoI, not mechanized.
- **CompCertO (Koenig & Shao, PLDI 2021) [V, author PDF].** Keywords include "Game Semantics"; §2.1 introduces game semantics as "a form of denotational semantics which incorporates some operational aspects", but semantics stay transition systems (§2.2: "Under the traditional CompCert semantics, programs are interpreted as transition systems which define strategies for the game E → W"; CompCertO generalizes the interfaces of these transition systems), and the correctness proofs are CompCert-style simulations under "simulation conventions". Operational, game-inspired interfaces. Contrast only.

---

## Synthesis: candidate novelty claims

| # | Candidate claim | Verdict | Safe phrasing |
|---|---|---|---|
| C1 | "First mechanized compiler-correctness proof using denotational semantics" | **Contradicted** by Chlipala07 (Coq, every intermediate language), Benton–Hur 2009 (source), XiaITrees20 (Imp/Asm), Cheng et al. 2026 (CompCert front end), and long before them by Polak 1980/81 (denotational source and target, compiler program machine-checked with the Stanford verifier, semantic theory by hand) and, per Polak, Milner–Weyhrauch 1972 and Cohn 1979 in LCF; also Martin–Toal 1991 (HOL) and Bourke et al. 2025 (Vélus). All of the pre-2007 ones are first-order. | Do not claim. Cite Chlipala, Benton–Hur, ITrees and Cheng et al. as the modern denotational line, and Polak (with the LCF work) as the historical mechanized one. |
| C2 | "First verified compiler whose correctness is proved with graph-model semantics" | **Supported, to our knowledge.** The only prior mechanized graph-model transformation proof is Siek's 2017 inliner (same language). PLFA has none. | "To our knowledge, this is the first verified multi-pass compiler, beyond same-language optimizations [Siek 2017], whose correctness is stated and proved using graph-model (Plotkin/Engeler-style) denotational semantics for every intermediate language." |
| C3 | "First denotational proof of closure conversion" | **Contradicted as stated** (Chlipala07 CPS→CC). Wand91 handles procedure representations on paper in an equational λ-theory, which is not a denotational semantics (see the entry above), so it is related work but not a counterexample. **Qualified version supported:** first for a source with general recursion and divergence (and recursive types, plus an untyped variant), denotation to denotation, mechanized. | "Unlike Chlipala's typed, total source, ours has general recursion through iso-recursive types; to our knowledge this is the first mechanized denotation-to-denotation proof of closure conversion for such a language." |
| C4 | "First mechanized denotational correctness proof of a compiler from a higher-order language with general recursion to assembly" | **Qualified.** Benton–Hur 2009 is mechanized, with recursion, but compiles to an SECD machine with closures (one pass, no closure conversion, operational target). VLISP is untyped Scheme to byte code but on paper. Chlipala07 is total. | "…the first mechanized compiler from a higher-order language with general recursion to an assembly language in which every pass, including closure conversion, is proved using denotational semantics." Keep "to our knowledge". |
| C5 | "Per-pass correctness is equality of denotations, ⟦src⟧ ≃ ⟦tgt⟧" | **Qualified, as a distinguishing feature, not a priority claim.** Chlipala uses type-indexed logical relations; Benton–Hur uses realizability. The Wand–Clinger single-model approach also equates meanings in one model (on paper). | "For most passes, correctness is literally equality of graph-model denotations; only closure lowering needs a relation." |
| C6 | "New approximant logical relation between two graph-model denotations" | **Supported, to our knowledge** (per the prior notes, Part B: no denotation-to-denotation relation indexed by finite elements was found). Polak 1980 (§IV.5.3.4–5) adds one more heterogeneous source/target predicate family, recursive and non-monotone, whose existence is assumed by appeal to Reynolds 1974; not indexed by finite elements. Gaps: Filinski 2007's construction and the primary texts of Milne–Strachey, Stoy and Mulmuley are unread. | "To our knowledge, the first relation between two denotational semantics indexed by a finite approximation on one side." |
| C7 | "First mechanized adequacy of a graph model (or of any denotational semantics) for an assembly language against an abstract machine" | **Supported, to our knowledge.** Chlipala and ITrees give assembly denotations without machine adequacy. VLISP's byte-code faithfulness (M92B093, now read) is on paper and one direction only. Polak's target machine has only a denotation (no machine, no adequacy). Tune & Kavvos 2026 mechanize CK/CEK machines in Agda (artifact description only; not assembly). | "To our knowledge, the first mechanized adequacy proof for a denotational (graph-model) semantics of an assembly-level language." |
| C8 | "End-to-end: source and compiled x86 both stop with the same constant or both diverge, via denotations plus adequacy at both ends" | **Qualified.** Benton–Hur proves both directions for SECD; ITrees gives termination-sensitive bisimulation (Imp/Asm); Chlipala gives termination for a total source. New in combination: higher-order with recursion, closure conversion, assembly, adequacy at both ends. | State the theorem and compare; avoid "first end-to-end". |
| C9 | "Same compiler also proved in three operational styles; controlled comparison" | **Supported, to our knowledge, for denotational versus operational.** Leroy & Grall (2009) and Danielsson (2012) are precedents for different *operational* styles on one (one-pass) compiler. Martin & Toal 1991 (HOL) give one toy imperative language and stack machine both a direct denotational and an SOS treatment in two case studies (abstract only; whether it is the same compiler is unverified): a one-pass, first-order precedent for denotational-and-operational in a proof assistant. | "To our knowledge, the first side-by-side mechanization of one multi-pass compiler in a denotational style and in three operational styles." |
| C10 | "Agda `--safe`, standard library only, no postulates" | **Engineering claim, qualified.** BahrHutton22 uses sized types and `TERMINATING` pragmas, with termination proved separately [V README]. Danielsson12 uses workarounds for productivity [V]. MossesCockxReus26 postulates domain constructors [A]. Whether sized types are rejected by `--safe` in current Agda is [M]. | "Fully `--safe` Agda: no postulates, no termination or productivity pragmas, no coinduction." |

No verdict changed in the gap-closing pass. C1 gains older counterexamples (Polak, the LCF work, Martin–Toal) and stays "do not claim"; C6, C7 and C9 gain notes but keep their safe phrasings; C2, C3, C4, C5, C8 and C10 are unaffected.

### Final searches (2026-10-15)

- **Run:** OpenAlex title/abstract search ("graph model" + "compiler correctness"; "filter model" + "compiler correctness"; "filter model" + compiler; "denotational semantics" + "closure conversion"; "adequacy" + "assembly language" + "denotational semantics"; "denotational" + "compiler correctness" + mechanized; "logical relation" + "two denotational semantics"; "denotational semantics" + compiler + Agda); the arXiv API abstract search (graph model/filter model/intersection types with compiler; denotational with closure conversion, compiler correctness, verified compiler, or a proof assistant name; adequacy with assembly or x86; "elementary model"); and web searches for the same combinations.
- **Blocked:** Google Scholar (HTTP 429 on every query), Semantic Scholar API (429, retried), DBLP (bot check on both dblp.org and dblp.uni-trier.de), ACM DL (403). No Scholar or DBLP sweep was completed.
- **Hits that touch a claim:** Martin & Toal 1991 and Bourke et al. 2025 (C1; C9 note), Tune & Kavvos 2026 (adjacent to C7), Rodríguez–Pagano–Fridlender 2016 and Brack 2026 (contrast). Nothing found affects C2, C3 or C6. The only graph-model closure-conversion hits are this project's own public GitHub issues and pull requests (a double-blind concern, not a novelty one).

### Remaining unverified gaps (check before submission)

1. **Polak's book (LNCS 124, 1981)** was not seen; the thesis (STAN-CS-80-802) was read. Cite the book for the published version, but the quotes above are from the thesis.
2. **Milner–Weyhrauch 1972, Cohn 1979, Martin–Toal 1991:** known only through Polak's description or an abstract. Read them before describing them in more than one line, in particular whether Martin–Toal prove the same compiler twice.
3. **Pardo et al. 2018:** the paper body (only the abstract and the 2016 slides were seen).
4. **Bahr–Hutton 2022 §3 prose:** checked against the artifact, not the paper text.
5. **Tune & Kavvos, ICFP 2026:** read the paper if C7 is phrased in terms of abstract machines rather than assembly.
6. **Not checked: "Kavvos"** in the earlier sense (no compiler-correctness paper found; dropped). The 2026 ICFP paper above is the only new Kavvos hit.
7. **Not checked: Hutton & Wright, "Compiling exceptions correctly", and other paper-only calculational works.** Mention generically.
8. **Google Scholar and DBLP full-text sweeps** could not be run (blocked). OpenAlex and arXiv found nothing affecting C2/C3/C6/C7, but they search titles and abstracts only.
