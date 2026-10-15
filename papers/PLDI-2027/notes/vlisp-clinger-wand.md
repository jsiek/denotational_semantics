# VLISP, Clinger 1984, Wand 1991/1992: closure conversion? primitive closures? mechanized? how far down?

Date of check: 2026-10-15. Primary sources read in full or in the relevant parts (text extracted with
dvips/ps2pdf/pdftotext):

| file | source | provenance |
|---|---|---|
| `overview.txt` | Guttman, Ramsdell, Wand, "VLISP: A Verified Implementation of Scheme" | author preprint `overview.ps.gz` (TeX 1994-11-09) from https://www.ccs.neu.edu/home/wand/papers/vlisp/lasc/ ; preprint pages 1–28 (LASC pages 5–32) |
| `scheme.txt` | Guttman, Swarup, Ramsdell, "The VLISP Verified Scheme System" | author preprint `scheme.ps.gz` (1994-11-09), same directory; preprint pages 1–78 (LASC 33–110) |
| `prescheme.txt` | Oliva, Ramsdell, Wand, "The VLISP Verified PreScheme Compiler" | author preprint `prescheme.ps.gz` (1994-12-07), same directory; preprint pages 1–72 (LASC 111–182) |
| `mfps-91.txt` | Wand, "Correctness of Procedure Representations in Higher-Order Assembly Language" | author DVI `papers/mfps-91.dvi` (TeX 1994-06-29) from Wand's page; preprint pages 1–18 |
| `lfp-92.txt` | Wand & Oliva, "Proving the Correctness of Storage Representations" | author DVI `papers/lfp-92.dvi` (TeX 1992-11-03) |

Page numbers below are **preprint** page numbers (the number printed in the extracted text). The
mapping to journal/LNCS pages is not verified page-by-page; for the LASC papers the preprints are
typeset in the Kluwer style with "1{28", "1{78", "1{72" page ranges, consistent with an offset.

**Not obtained:** Clinger 1984 (ACM DL returned 403; Semantic Scholar marks it CLOSED; no copy on
Internet Archive). The MITRE reports (M92B092 byte-code compiler, M92B093 faithfulness, M92B094
flattener, M92B095 linker) were not found online. Everything said about Clinger 1984 below comes from
**secondary descriptions in the VLISP/Wand papers** and is flagged as such.

---

## BibTeX

```bibtex
@article{GuttmanRamsdellWand95,
  author  = {Joshua D. Guttman and John D. Ramsdell and Mitchell Wand},
  title   = {{VLISP}: A Verified Implementation of {Scheme}},
  journal = {Lisp and Symbolic Computation},
  volume  = {8}, number = {1/2}, pages = {5--32}, year = {1995}
  % DOI not verified (web search gave both 10.1007/BF01128406 and BF01128408 for VLISP articles)
}
@article{GuttmanRamsdellSwarup95,
  author  = {Joshua D. Guttman and John D. Ramsdell and Vipin Swarup},
  title   = {The {VLISP} Verified {Scheme} System},
  journal = {Lisp and Symbolic Computation},
  volume  = {8}, number = {1/2}, pages = {33--110}, year = {1995}
}
@article{OlivaRamsdellWand95,
  author  = {Dino P. Oliva and John D. Ramsdell and Mitchell Wand},
  title   = {The {VLISP} Verified {PreScheme} Compiler},
  journal = {Lisp and Symbolic Computation},
  volume  = {8}, number = {1/2}, pages = {111--182}, year = {1995}
}
@techreport{VLISPFaithfulness92,
  author      = {William M. Farmer and Joshua D. Guttman and Leonard G. Monk and John D. Ramsdell and Vipin Swarup},
  title       = {The Faithfulness of the {VLISP} Operational Semantics},
  institution = {The MITRE Corporation}, number = {M92B093}, month = sep, year = {1992}
  % bibliographic data from secondary citations only; report not seen
}
@inproceedings{Clinger84,
  author    = {William Clinger},
  title     = {The {Scheme} 311 Compiler: An Exercise in Denotational Semantics},
  booktitle = {Proceedings of the 1984 ACM Symposium on LISP and Functional Programming (LFP '84)},
  pages     = {356--364}, year = {1984},
  doi       = {10.1145/800055.802052}
}
@inproceedings{Wand91,
  author    = {Mitchell Wand},
  title     = {Correctness of Procedure Representations in Higher-Order Assembly Language},
  booktitle = {Mathematical Foundations of Programming Semantics (MFPS '91)},
  series    = {LNCS}, volume = {598}, pages = {294--311},
  publisher = {Springer}, year = {1992},
  doi       = {10.1007/3-540-55511-0_15}
}
@inproceedings{WandOliva92,
  author    = {Mitchell Wand and Dino P. Oliva},
  title     = {Proving the Correctness of Storage Representations},
  booktitle = {Proceedings of the 1992 ACM Conference on LISP and Functional Programming (LFP '92)},
  pages     = {151--160}, year = {1992}   % pages from memory, UNVERIFIED
}
```

---

## 1. VLISP (1995 LASC papers)

### Pipeline (Scheme side)

GSS 1995 (`scheme.txt`), p. 2:

> "A simple compiler that translates programs in the source language to target programs in an
> intermediate level byte code language; An interpreter (written in a systems-programming oriented
> dialect called PreScheme [10]) to execute the resulting byte code programs; A second compiler to
> translate the PreScheme code of the interpreter into assembly language code for a commercial
> workstation."

GSS p. 3: the byte-code compiler "rewrites the Scheme source code into a tree-structured byte code
based on Clinger's target language [1] ... basic byte code or bbc"; the flattener produces "flattened
byte code (fbc)"; further layers (tabulator, linker, image builder; p. 5) produce "Stored Byte Code or
sbc ... the form that is loaded and executed by the vlisp Virtual Machine."

GSS p. 5, Table 1 "vlisp Verification Steps": Byte Code Compiler (Scheme, bbc); Faithfulness (bbc,
bbcm); Flattener (bbc, fbc); Procedural Instantiation (sbc, sbcm); Garbage Collector (sbcm, gcsm);
Finiteness (gcsm, fsbcm).

So: **Scheme -> (byte-code compiler) -> bbc -> (flattener) -> fbc -> (tabulator/linker/image builder)
-> sbc, executed by an interpreter (the VM)**. The Scheme program is never compiled to assembly; the
*interpreter* (VM, written in PreScheme) is compiled to assembly by the separate PreScheme compiler.

### Primitive closures in the byte code and VM

Basic byte code grammar (GSS p. 11, Table 3) includes the instruction `<closure t>` (with `t ::= <lap c b>`
a code template), plus `<make-env n>`, `<local n1 n2>`, `<make-cont b1 n>`, `<call n>`, `<return>`.

Operational semantics of bbc (GSS p. 32, Table 13): values

> "v ::= c | <closure t u l> | <escape k l> | <mutable-pair l1 l2> | ..."

and the Call rule (GSS p. 33, Table 14):

> "Rule 3: Call. Domain conditions: b = <<call #a>>; v = <closure t1 u1 l1>; t1 = <lap c b1>.
> Changes: t' = t1 u' = u1 b' = b1"

Denotational side (GSS p. 19): "A similar relation links call to the auxiliary closure, which creates
procedure values." Faithfulness clause (GSS p. 35, Table 16): "Dv[<closure t u l>] = ..." (closure
values are given denotations directly).

At the bottom (Stored Byte Code machine, GSS pp. 54–56), closures are heap "stored objects" with header
tag `closure` (Table 23: "dhtag ::= pair | symbol | vector | location | template | closure | port |
continuation | environment"), and the call rule (Table 24) requires "S(v, s) = <closure false <t1 u1 d1>>"
and sets "t' = t1, n' = 0, u' = u1". The VM code (GSS p. 59):

> "(assert (closure-stob? (value-ref)) "op/call: value register does not contain a closure")
> (template-set (stob-ref (value-ref) 0)) ;; Closure's template
> (env-set (stob-ref (value-ref) 1)) ;; Closure's env"

**Reading:** the compiler's target language (bbc ... sbc) has closure *creation* and closure *call* as
primitive instructions; the closure is a pair (code template, environment) built by the machine from
the *current* linked run-time environment (Clinger/Scheme48 linked frames/"display ribs" with
two-dimensional lexical addresses, GSS p. 9: "calculates two-dimensional <over; down> lexical
addresses"). The representation of closures as heap records (template + env pointer) appears only as a
**data refinement of the interpreter's state** (storage-layout relations between state machines),
not as a source-to-source pass that turns higher-order procedures into first-order data. There is no
free-variable analysis / flat-closure construction / code hoisting pass in the Scheme compiler.

### PreScheme compiler (the path to assembly)

ORW 1995 (`prescheme.txt`), p. 5:

> "A compiler for this language will reject any program that requires dynamic type checking or
> creation of closures at run-time." ... "lambda expressions in Pure PreScheme programs may occur only
> as initializers in top-level letrec bindings, or in the operator position of a procedure call. As a
> result, there is no need to represent closures at run-time. Finally, Pure PreScheme's syntax forbids
> non-tail-recursive procedure calls."

ORW p. 9 (validity conditions):

> "A valid vlisp PreScheme program can run without creating closures at run time. Thus, if p is a
> pointer to a procedure, the free variables of that procedure must be allocatable at compile time.
> However, a vlisp PreScheme program may textually contain procedures with free variables that are
> lambda-bound. The compiler must transform these programs so that they meet the run-time restriction."

The front end does this with verified rewrite rules: "simplifiers, β-reduction, inlining, and
lambda-lifting" (p. 5); "The remaining categories of rules implement β-conversion, closure hoisting, and
defined constant substitution ... Closures are hoisted by the use of several other rules" (p. 20). The
front end may not terminate (overview p. 8: "the Front End does not terminate for all inputs").

So PreScheme's compiler **eliminates** closures (β/inlining/lambda lifting/hoisting; programs that
genuinely need run-time closures are rejected) rather than **converting** them into code+environment
records. Its target never has closures at all.

### Proof methods: denotational vs operational

Overview (`overview.txt`), p. 2:

> "1. Semantics-preserving source-to-source transformations. 2. Structural inductions using the
> denotational semantics, in the fashion of Wand and Clinger [31, 3]. 3. Verification of representations
> and refinements using operational semantics and the method of storage layout relations [32]. 4. The gap
> between denotational and operational semantics is bridged by soundness or faithfulness proofs; for the
> PreScheme compiler an adequacy result was achieved as well."

Overview pp. 13–14: compiler step "A syntax-directed compiler in the Wand-Clinger style ... The proof
establishes an equality (or a strong equivalence) between the denotations of its input and output";
then "A succession of representation decisions and optimizations. These steps are justified by
reference to an operational semantics, by supplying proofs that one state machine refines another."
Overview p. 18: after the switch to operational, the remaining steps were "responsible for linearizing
code, for implementing the primitive data structures of the languages, for representing the stack and
environment structures, for introducing garbage collection in Scheme, and for omitting type tags in
PreScheme."

GSS p. 6: faithfulness only, not adequacy, for Scheme: "it does not establish the converse: namely,
when the denotational semantics predicts that p will evaluate to a particular answer, then the state
machine actually delivers it." Finite machine is partial correctness only (GSS p. 4: "it is correct
only in the sense that when it does compute an answer, that is the same value that the gcsm would have
computed. This is a sort of partial correctness.").

Denotational: Scheme -> bbc (Clinger-style, same domains), PreScheme front end and PreScheme -> combinator
code. Operational: everything after (flattener, linker/image, VM refinements incl. GC; PreScheme
linear-data and stored-program machines).

### How far down

ORW p. 4:

> "the algorithms are verified with respect to a formal denotational semantics of PreScheme and a formal
> model of an abstract target machine. The implementation of the algorithms was carried out in Scheme,
> and code for the abstract target machine was translated into assembly language for two real target
> machines (Motorola 68000 and SPARC). While neither of these implementation steps was verified, both
> were straightforward"

So verification stops at an abstract stored-program machine (PreScheme side) and the finite stored
byte code machine (Scheme side); the 68000/SPARC assembly emission and the code itself are unverified
("algorithm-level verification", overview p. 2: "Our goal was to verify the algorithms and data types
used in the implementation, not their embodiment in code").

### Mechanized?

GSS p. 76 (Conclusion): "**Proofs have not been checked using a mechanical theorem prover.**"
Also GSS p. 3: "We have not produced derivations in a particular formal deductive system." and overview
p. 2: "The verification was intended to be rigorous, but not completely formal". Some proofs were done
only for representative cases (GSS p. 76: "only cases that appeared to us to be 'representative' or
'interesting' were selected for detailed proof").

### Verdict — VLISP

- performs closure conversion: **no** (Scheme byte-code compiler keeps closures primitive; heap layout of
  closures is a verified *VM data refinement*, not a compiler pass; PreScheme compiler eliminates
  closures by inlining/lambda-lifting/hoisting and rejects programs that need them).
- target has primitive closures: **yes** (bbc `<closure t>` instruction, `<closure t u l>` values, `call`
  on closures; SBC heap objects tagged `closure` interpreted by the VM).
- mechanized: **no** (explicit statement, GSS p. 76).
- how far down: Scheme -> byte code, executed by a verified-at-algorithm-level interpreter refined to a
  finite stored-byte-code machine; the interpreter is compiled by the PreScheme compiler to an abstract
  stored-program machine; the 68000/SPARC assembly step "was not verified". Language/system is Turing
  complete with divergence (full Scheme), denotational top proof, but only faithfulness (no adequacy)
  for the Scheme side.

---

## 2. Clinger 1984, "The Scheme 311 Compiler: An Exercise in Denotational Semantics"

**Primary source not seen** (ACM DL 403; no open copy found). The following is what the VLISP/Wand
papers say about it; treat as secondary.

- Target is a tree-structured byte code with a denotational semantics in the same domains as Scheme;
  each instruction's denotation acts on registers + store (overview p. 16: "In the Scheme byte compiler,
  for instance, we follow Clinger [3] in giving each instruction a denotation that may be regarded as
  acting on four registers together with a store"). VLISP's bbc is "based on Clinger's target language"
  (GSS p. 3), and bbc contains a primitive `<closure t>` instruction (see above). That Clinger's own
  target has an equivalent closure-creating instruction is **likely but unverified** from the primary
  source.
- Wand & Oliva 1992 (`lfp-92.txt`, p. 2): "In this approach, the target language was a sublanguage of
  the λ-calculus, designed to be closed under reduction. The target machine simply had to simulate the
  reduction of the target program. ... This approach was refined by Clinger [3] to prove the correctness
  of a compiler for Scheme."
- ORW (`prescheme.txt`) p. 46: "Clinger used a value register ... and a value stack"; "Clinger's compiler
  used two different compiling valuations ... (for general expressions) and ... (for expressions in tail
  position) ... [5, Figure 5]"; p. 47 quotes Clinger: "... the algorithm was designed and a compiler built
  before any thought was given to a formal correctness proof." [5, page 356]. GSS p. 28 attributes the main
  inductive lemma ("Clinger's Lemma") to Clinger and says its proof cases are "very similar in manner to
  Clinger's original proof [1]".
- Method (secondary): a Wand-style proof — source and target share domains; correctness = equality of
  denotations; structural induction on source syntax; paper-and-pencil.

### Verdict — Clinger 1984 (from secondary sources; primary not seen)

- performs closure conversion: **no (unverified from primary)** — no secondary source mentions any closure
  representation pass; its descendant (VLISP bbc) has primitive closures.
- target has primitive closures: **yes (unverified from primary)** — inferred from VLISP bbc being "based on
  Clinger's target language" and having `<closure t>`.
- mechanized: **no** (paper proof; consistent with 1984 and with Clinger's quoted remark; no claim of
  mechanization anywhere).
- how far down: to a denotationally specified byte-code/abstract machine (the target-language "λ-calculus
  sublanguage" per Wand & Oliva); not to real assembly (unverified from primary).

---

## 3. Wand, MFPS 1991 (LNCS 598, 1992), "Correctness of Procedure Representations in Higher-Order Assembly Language"

### What HOAL is

Abstract (p. 1):

> "Higher-order assembly language (HOAL) generalizes combinator-based target languages by allowing free
> variables in terms to play the role of registers. We introduce a machine model for which HOAL is the
> assembly language, and prove the correctness of a compiler from a tiny language into HOAL. We introduce
> the notion of a λ-representation, which is an abstract binding operation, show how some common
> representations of procedures and continuations can be expressed as λ-representations. Last, we prove
> the correctness of a typical procedure-calling convention in this framework."

HOAL terms are λ-terms in CPS: "add r1 r2 (λr3.C)" with "add = λxyκ.κ(x + y)" (p. 2). The machine state is
"a pair ⟨C, ρ⟩ consisting of an HOAL term C and a substitution ρ mapping λ-variables ... to constants or
closed abstractions" (p. 2); the machine is derived from β-reduction: "given a denotational semantics for
our machine instructions, we derive an operational semantics by inheriting the operational semantics of
the λ-calculus" (p. 3).

### Source language and correctness criterion

Source: variables, `+`, then `(proc I.M)` and `(M N)` (pp. 5, 7, 15). No recursion construct, no types
(p. 16: "our source language is not type-secure"). Correctness (p. 6): "C[[M]]K = E[[M]]K, where equality
means interconvertibility under the rules of the λ-calculus". Conclusion (p. 17): "we can reason about the
semantics and the compiler in the same λ-theory, and the operational semantics is derived from the
denotational semantics by looking at the reduction behavior of the λ-terms."

### Procedure representations

Section 6 ("A Simple Procedure Design"): the machine has primitive closures: "The close instruction creates
a closure of two arguments which represents a procedure ... we assume that the machine copies the contents
of the current register set into some data structure (a closure)" (p. 9).

Section 5 lists, as a λ-representation, "A closure representation, in which a λ-abstraction is represented
as a record consisting of a closed λ-term and a record of the free variables ... abs x.M ≡ [λ[u1,...,un]x.M,
[u1,...,un]], Ap ≡ λf.(f.1)(f.2)" (p. 8). Motivation (p. 7): "we want the compiled code for this procedure
to return a closure record, not a λ-abstraction."

Section 7 ("Explicitly Closed Procedures", p. 10): "We will use 'continuation-passing, closure-passing style'
[1], in which a procedure is represented by a record f whose first component (f.1) is a closed term
(executable code). ... Each procedure body begins with a preamble that extracts the procedure's local
variables from the closure record and puts them in the registers where they belong". "Theorem 2 This is a
correct λ-representation." The compiler then uses a `movec` instruction: "movec forms a record consisting
of its first argument (a pointer to some code) and the contents of the registers r1,...,rn" (p. 11), and
`jsr`/`rts` with continuations represented as stacks (pp. 12–15). Recursion is explicitly left aside: "A
cleverer representation might use the fact that App is passed the entire closure ... to bind a register
to the closure itself in order to handle recursion." (p. 10). The calling sequence is "not properly
tail-recursive" (p. 15), fixed by a sketched tail/non-tail split.

Representation independence (Section 9, p. 16): extend λ with uninterpreted `abs`/`Ap` plus axiom
"Ap(abs x.M) = λx.M"; "Theorem 3 λ + AP is a conservative extension of λ." (proof "sketch", via λ-models /
open term model). "Thus, if the term generated by the semantics ... reduces to a constant, we are guaranteed
that our compiled code will reduce to the same constant, independent of the choice of procedure
representation." (p. 17)

### Verdict — Wand 1991

**Classification (author, 2026-10-15): not a denotational semantics.** The meanings are λ-terms up to
interconvertibility, which is not extensional, and no model is used (except the open term model in the
sketched proof of Theorem 3). It is a compositional translation into an equational λ-theory. Representation
changes are easy there because a closure record is a single term, so `Ap(abs x.M) = λx.M` is a β-equation;
in a set-based model a closure denotes a set, and car and cdr can mix elements of it, which is what the
approximant logical relation handles.


- performs closure conversion: **partly** — Section 7 is a genuine closure-passing-style representation
  (records of closed code + free-variable values, `movec`, `jsr`/`rts`), proved correct as a
  λ-representation, but: for a tiny untyped language without a recursion construct (recursion explicitly
  deferred), as one representation step in an equational λ-theory, not a whole compiler; the "code" is still
  a closed λ-term and the machine is derived from β-reduction of HOAL terms.
- target has primitive closures: **yes in the Section 6 design** (`close` copies the register set into a
  closure); **no in the Section 7 design** (closures are records built by `movec`; code parts are closed
  terms). HOAL itself remains a λ-calculus, so "first-order" holds only for the data representation, not
  for the target language's syntax.
- mechanized: **no** (paper proofs; Theorem 3 proof is a sketch).
- how far down: an abstract register machine whose program is a HOAL λ-term (`move`, `add`, `movem`,
  `push`/`pop`, `jsr`, `rts`); not real assembly; storage/pointer issues "left to another layer" (p. 5).

## 3b. Wand & Oliva, LFP 1992, "Proving the Correctness of Storage Representations" (brief)

Source language (p. 2): "Its values are integers, recursive procedures, and continuations" with `catch`/
`throw`; "Procedures are recursive, using a local identifier for self-reference. Any kind of value may be
passed to a procedure, but procedures may return only integers, so that the language can be implemented
using only a stack." Byte-code machine has a `close` instruction: "(close π′ π)uζκ = πu(⟨proc, closure uπ′⟩ ::
ζ)κ" with "(closure uπ) = fix(λp.λvκ.π(extR⟨v,⟨proc,p⟩⟩u)⟨⟩κ)" (p. 3). Method (p. 1): "the translation from
source code to combinator trees is proved correct using structural induction and denotational reasoning; the
translation from the abstract machine to the the concrete machines is proved correct using induction on length
of execution and operational reasoning." The concrete machine stores display/stack/continuation in one stack
with static and dynamic links; "Values (integers or closures) are represented as single words in memory,
including their tags" (p. 4).

Verdict: closure conversion **no** (byte-code machine has a primitive `close`; the stack representation is a
storage-layout refinement of the abstract machine, restricted to a stack-discipline language with no upward
funargs); target has primitive closures **yes** (abstract machine); mechanized **no**; how far down: an
abstract stack/store machine with linear program representation, not real assembly.

---

## What this means for the title qualifiers

None of these works mechanizes anything, none compiles a higher-order language to real assembly with
verification reaching the assembly level, and none performs a closure-conversion *pass* on a Turing-complete
language as part of a whole verified pipeline:

- VLISP: whole system, Turing complete, denotational top proof, reaches (unverified) 68000/SPARC only via the
  interpreter; Scheme compiler target has primitive closures; PreScheme eliminates closures rather than
  converting them; not mechanized.
- Clinger 1984: (secondary sources) target byte code with closures; paper proof.
- Wand 1991: the closest to an equational (not denotational; see §3) proof of closure conversion, but a single
  representation step for a tiny untyped language without recursion, target still λ-terms, paper proof.

So the combination "denotational + higher-order + recursive types + through closure conversion + to assembly"
is already distinguishable from these works **without** "mechanized": VLISP fails "through closure conversion"
(and "to assembly" for the Scheme program itself; its assembly step is unverified), Wand 1991 fails "to
assembly", "recursive types"/Turing-complete source, and whole-compiler, and Clinger fails "through closure
conversion" and "to assembly". However, the paper-and-pencil prior art (VLISP especially) is strong enough that
reviewers would naturally ask "how is this different from VLISP?"; "mechanized" is the cleanest single word that
answers that, and it is also true of all three. Recommendation: keep "mechanized" if the qualifier list is meant
to be a precise novelty claim against the 1980s–90s denotational compiler-correctness line; it is not strictly
needed to separate from these three works (closure conversion + assembly already do that), but dropping it
makes the claim rest on finer distinctions (VLISP's VM-level closure representation vs a compiler pass; Wand's
λ-representation vs a whole pipeline).
