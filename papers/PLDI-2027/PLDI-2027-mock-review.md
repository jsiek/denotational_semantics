**Bottom line** This is a technically strong and unusually ambitious paper with a credible central novelty: the approximant logical relation used to prove reflection for closure conversion. I would score it B in the traditional PLDI scale. The main obstacle to an A is not the core proof, but the framing of the proof-size comparison. The headline ranking omits the graph model's adequacy proof even though the operational columns already state execution-level theorems. The paper should separate the mathematical comparison of pass proofs from the end-to-end cost of reaching an operational guarantee.

# Review Form

| **Field** | **Assessment** | **Rationale** |
|----|----|----|
| Paper score | B | OK paper, but I would not yet champion it |
| Reviewer expertise | Y | Knowledgeable in semantics, mechanized metatheory, and compiler correctness; not a graph-model specialist |
| Accuracy | 4 of 5 | The technical story is coherent and mechanized; artifact inspection remains important |
| Significance | 4 of 5 | The reflection proof addresses a real gap, though the compiler target is deliberately abstract |
| Originality | 4 of 5 | The finite-target approximant relation appears novel and well motivated |
| Clarity | 4 of 5 | Strong exposition overall, with several correctable inconsistencies and repetitive framing |

# Paper Summary

The paper mechanizes in Agda the correctness of a ten-pass compiler from a call-by-value lambda calculus with iso-recursive types to a typed assembly language. Nine passes preserve graph-model denotations by equality. The difficult pass, delay, replaces semantic functions with explicit code-environment pairs. Its target denotation contains junk code-environment combinations, so reflection cannot be proved with a simple elementwise relation. The paper introduces an approximant logical relation between a whole source denotation and a finite list of target graph elements, indexed by target-element depth. A fundamental lemma yields preservation and reflection of constants and nonemptiness. Adequacy connects the source and target graph semantics to clocked interpreters.

The paper also implements four comparison developments: Scott-domain denotations, abstract machines, clocked interpreters, and reduction semantics. It compares lines of Agda per compiler pass and argues that denotational equations are concise when value representations remain stable, while operational proofs are substantially shorter for closure lowering.

# Points in Favor

- The reflection problem is substantive. The paper identifies why code and environment components can mix in the target denotation and why that defeats several natural relation shapes.

- The approximant logical relation is a clean conceptual contribution. Relating a finite target approximation to the whole source denotation gives both the information needed to match mixed components and a well-founded depth measure.

- The paper does more than present one pass in isolation. It connects the result to a complete typed pipeline, states the endpoint adequacy theorem, and supplies mechanized proofs.

- The comparison across five semantic styles is unusually broad. Even if line count is imperfect, the pass-by-pass breakdown reveals a useful qualitative pattern that would be difficult to see from isolated case studies.

- The exposition is generally excellent for a dense semantics paper. The running junk-entry example, the failed-relation taxonomy, and the separation of preservation from reflection are especially effective.

- The manuscript follows the PLDI 2027 requirements on AI-use disclosure, data availability, and supplying mechanized proofs in spirit, assuming the promised anonymized supplement is included.

# Points Against

- The headline proof-size ranking is not fully like for like. The graph-model column ends at a denotational theorem; the operational columns end at execution equivalence. The 1,529-line graph adequacy development is reported separately. Adding it changes the graph route to an interpreter-level theorem from 1,806 to 3,335 lines, above all three operational totals reported in Table 1.

- The comparison remains sensitive to accounting choices. Language-independent infrastructure differs sharply by style, and the paper excludes it from the totals. The paper reports those figures, but the abstract and conclusion state a simple ranking more strongly than the methodology supports.

- The assembly endpoint is a typed abstract machine language with an abstract heap, only three registers, no register allocation, acyclic control flow, and a case pseudo-instruction. The proof is valuable, but the title and repeated phrase 'to assembly' may invite a realism objection unless the paper foregrounds these limits.

- The correctness theorem is whole-program and observationally coarse. For arbitrary result types it preserves constants and nonemptiness; the clean execution claim is later specialized to integer programs. This is weaker than contextual or separate-compilation correctness and should be stated more prominently.

- All five developments were produced by the same authors and largely by the same AI coding workflow. This is not a validity defect, but it is a confound for claims about proof-style effort or concision. The paper measures a particular implementation outcome, not author effort or inherent proof complexity.

- Several visible editing defects weaken confidence in submission readiness: five research questions are introduced as four; the abstract refers to four whole-compiler proofs after describing five developments; Contribution 4 contains 'when a the relation'; and the keyword field is still TBD.

# Detailed Comments for the Authors

1.  **Separate the two evaluation questions.** Table 1 is informative as a comparison of pass proofs relative to each style's chosen semantics. It does not by itself compare the full cost of proving that generated code executes like the source. Please present both views: the current per-pass table, and an end-to-end table that includes adequacy or otherwise aligns all endpoints. The abstract, Section 5.4, and conclusion should use the narrower claim unless the latter table supports the broader one.

2.  **Report sensitivity to accounting choices.** The manuscript already gives infrastructure counts and acknowledges uneven sharing. Bring those numbers closer to Table 1 and add totals under at least three policies: pass proof plus language semantics; all style-specific infrastructure; and the route to a common operational observation. This would turn the current threat into a result readers can evaluate.

3.  **Clarify the theorem's observational strength.** Theorem 4.1 preserves constants and nonemptiness, while the strongest operational statement in Section 4.3 is for integer-typed programs. Explain what is and is not preserved at function, tuple, sum, and recursive types; state explicitly whether wrong answers or errors are ruled out for all well-typed closed programs; and distinguish whole-program correctness from contextual correctness.

4.  **Calibrate the assembly claim.** A reviewer may read x86 in the title and expect a concrete ISA model. Either rename the endpoint more plainly as a typed assembly-like IR or add a short paragraph near the first use of x86mu listing the abstractions that remain and why they do not trivialize the closure-conversion result.

5.  **Make the approximant relation easier to audit.** The key idea is convincing, but Figure 4 is dense. Extend the 9 + y example through one complete target call: identify the finite list V, its usable entry, the argument list U, the result list W, and the corresponding source application. This would help a reader check Clause 3 before reading the mechanization.

6.  **Strengthen the artifact handoff.** The Data-Availability Statement gives versions and approximate checking time. The supplement should also identify the exact commands for the graph, operational, adequacy, and Scott-domain checks; the pinned TypeTopology commit and patch; the files containing each theorem statement; and the script invocation that reproduces Table 1. Because mechanized proofs are a principal contribution, these are review-critical rather than post-acceptance polish.

7.  **Tighten novelty language.** The paper's 'first' claims are plausible and supported by a serious related-work section, but they are broad. Frame the novelty as the specific combination actually established: a mechanized, denotational preservation-and-reflection proof for closure conversion with general recursion, using a one-sided finite approximant relation. This is already a strong claim and is easier to defend.

8.  **Fix the submission-level defects.** Change 'four research questions' to 'five'; resolve 'four whole-compiler correctness proofs' versus five developments; correct 'when a the relation'; fill the keywords; and spell 'Adequacy' consistently. These are small changes, but the first two occur in the framing of the paper's main claims.

# Questions for the Authors

- If the common endpoint is interpreter behavior, why should the 1,529-line adequacy proof be excluded from the graph-model total while the operational styles require no analogous bridge?

- Can the qualitative per-pass conclusion be shown to survive alternative accounting policies, including all style-specific infrastructure and adequacy?

- What exactly is the strongest observation preserved for closed programs of non-integer type, and how does that compare with the observations used by the three operational semantics?

- Which parts of the delay reflection argument rely on typing, and which would survive for the dynamically typed variant mentioned in the conclusion?

- Did the same cleanup rules and stopping criteria apply to the Scott-domain development, whose cleanup removed far more code than the other developments? Can you provide commit hashes before and after cleanup?

- Does the anonymized supplement contain every proof counted in Table 1 and a clean-room script that regenerates the table from a fresh checkout?

# Recommended Decision

**B OK paper but I will not champion it in its current form**. I would support conditional acceptance if artifact inspection confirms the central theorems and the revision substantially narrows or repairs the comparison claim. The approximant logical relation is strong enough to justify publication; the evaluation should not be allowed to overstate what the line counts establish.

# AI Generated Feel Audit

This section flags prose that has an AI-associated feel. It is a stylistic judgment, not evidence about authorship. Most of the paper does not read like generic AI prose: it uses concrete technical examples, states exact invariants, and explains failed proof approaches. The strongest signals are mechanical recap, repeated framing, and edit residue.

| **Location** | **Flagged wording or pattern** | **Assessment** | **Suggested revision** |
|----|----|----|----|
| Page 1 line 48 | These challenges motivate four research questions | High-confidence edit residue because five questions follow. It feels mechanically generated or incompletely revised. | Use 'five research questions.' |
| Abstract paragraph 2 and Introduction results paragraphs | Repeated ranking sentences and the same numeric contrasts | Medium. Repetition is normal across an abstract and introduction, but the cadence feels templated because the same list of styles and numbers recurs several times. | Let the abstract give the result; use the introduction to explain why the ranking changes by pass. |
| Introduction contribution 4 | which shows that the denotational proofs are among the smallest ... but are the largest ... when a the relation | High. The broad balanced contrast plus the 'a the' error reads like generated text that escaped a human edit. | State the measured fact directly and fix the article: 'The graph proof is shortest for two passes and longest for delay.' |
| Section 3 opening | We first explain ... then ... and then ... We end this section ... | Low. This is formulaic navigation, but it helps readers in a technical section. | Optional: compress to one sentence naming only the concepts needed later. |
| Section 5.3 paragraph headings | Three consecutive headings beginning 'When denotational correctness ...' | Medium. The symmetry is useful, but the repeated template has a generated taxonomy feel. | Keep the three cases, but shorten the headings to 'Aligned representations and runs,' 'Equal meanings but different runs,' and 'Changed representations.' |
| Section 5.4 | The comparison supports the answer to RQ2 ... The answer to RQ4 is mixed ... For RQ5 ... | Medium-high. This is a mechanical recap of claims already made in the introduction and Section 5.3. | Replace with one paragraph stating the boundary of the evidence and the accounting caveat. |
| Conclusion | A seven-sentence RQ1 through RQ5 checklist | High. The parenthetical RQ labels and one-result-per-sentence sequence feel auto-summarized rather than written as a conclusion. | Conclude with the central technical lesson: denotational equality is effective until representation changes; the approximant relation repairs reflection but at substantial proof cost. |
| Throughout | Frequent phrases such as 'The answer to RQ2' and 'the reason that the answer to RQ3 is negative' | Medium. The language is clear, but repeated question-answer bookkeeping makes the prose sound procedural. | Use the RQ labels in the introduction and evaluation summary only; elsewhere state the technical point directly. |

# Committee Expertise Calibration

The following names are plausible expertise matches from the published PLDI 2027 Review Committee, not predictions of actual assignment. TPMS matching, workload, seniority, and conflicts can change assignments. The useful exercise is to anticipate the questions these expertise profiles are likely to raise.

| **Committee member** | **Public expertise match** | **Likely review lens** |
|----|----|----|
| Michael Norrish | CakeML, HOL4, mechanized programming-language semantics | Whether the operational theorem and artifact support match the compiler-correctness claim; fairness of comparison with CakeML-style interpreters |
| Daniel Patterson | Compiler-correctness theorem design and whole-program versus compositional compilation | The exact scope of the theorem, its closed-world assumptions, and whether preserving constants plus termination is the right correctness notion |
| Alex Kavvos | Denotational semantics, adequacy, type theory, and domain theory | Mathematical novelty of the one-sided finite approximant relation and the justification for the graph model over Scott domains |
| Dominique Devriese | Logical relations, Agda formalization, semantic typing, and verified systems | Well-foundedness and variance of the relation, correspondence between prose and mechanization, and artifact auditability |
| Peter Thiemann | Programming-language semantics, types, Agda, and program transformation | Clarity of the recursive-type story, closure representation, and whether the compiler is representative enough for the comparative claims |
| Steve Zdancewic | Verified compilation and proof-assistant-based systems; Associate Chair | Likely assignment or discussion lens on significance, end-to-end theorem strength, and revision scope rather than a prediction that he would personally review |

# Sources Used for Calibration

- [PLDI 2027 call for papers and evaluation criteria](https://pldi27.sigplan.org/track/pldi-2027-papers)

- [PLDI 2027 Review Committee](https://pldi27.sigplan.org/committee/pldi-2027-papers-pldi-review-committee)

- [Practices of PLDI review form and A through D scale](https://www.sigplan.org/sites/default/files/PracticesofPLDI.pdf)

- [Michael Norrish research profile](https://comp.anu.edu.au/people/michael-norrish/)

- [Daniel Patterson and Amal Ahmed on compiler correctness theorems](https://www.ccs.neu.edu/home/amal/papers/next700ccc.pdf)

- [Alex Kavvos research profile](https://www.bristol.ac.uk/people/person/Alex-Kavvos-a0f713ee-60aa-432b-8972-8017d1a939dd/)

- [Dominique Devriese publication profile](https://www.cs.kuleuven.be/publicaties/lirias/TEST2/mypubs.php?unum=U0043379)

- [Peter Thiemann programming languages group](https://proglang.informatik.uni-freiburg.de/teaching/proglang/2023ws/)

*Prepared as an independent mock review on 22 October 2026*
