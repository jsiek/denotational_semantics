# Related work: closure conversion, denotational semantics, and mechanized proofs

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

- **Nielsen, "A Denotational Investigation of Defunctionalization", BRICS RS-00-47, 2000.** [abstract]
  <https://www.brics.dk/RS/00/47/>
  - Defunctionalization is closure conversion's first-order cousin.
  - The paper gives a denotational proof, via logical relations, for a *typed* language. It shows that every terminating program keeps its meaning.

- **Banerjee, Heintze, Riecke, "Design and Correctness of Program Transformations Based on Control-Flow Analysis", TACS 2001, LNCS 2215.** [abstract]
  <https://link.springer.com/chapter/10.1007/3-540-45500-0_21>
  - Proves defunctionalization correct, then uses that proof to prove flow-based inlining and lightweight defunctionalization correct.
  - The abstract does not say whether the method is denotational; check the full text.

- **Wand and collaborators: denotational and "almost-denotational" proofs of closure-related transformations.** [abstract]
  Index: <https://www.khoury.northeastern.edu/home/wand/analysis-papers.html>
  - Wand, "Correctness of Procedure Representations in Higher-Order Assembly Language", MFPS 1991, LNCS 598.
  - Wand & Steckler, "Selective and Lightweight Closure Conversion", POPL 1994; journal version Steckler & Wand, TOPLAS 1997. Correctness is justified by flow-analysis constraints.
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
6. **Nielsen 2000 and Banerjee–Heintze–Riecke 2001.** Denotational proofs for defunctionalization.
