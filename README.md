# denotational_semantics
Denotational semantics based on graph and filter models

## The closure-conversion compiler

`agda/All.agda` gathers a compiler from ISWIM to X86ᵀ, a typed assembly
language, with closure conversion and intrinsically typed intermediate
languages, and its
correctness proofs, in five styles (denotational: graph model; CEK
machine + simulation, after CompCert; clocked interpreter + value
relations, after CakeML; reduction semantics + simulation, by
substitution; and the graph model with errors), with the adequacy of the
two graph models for the machines:

    ISWIM --simplify--> ISWIM --cast insertion--> ISWIMᵀ --CC: capture--> Clos2ᵀ
          --CC: prune--> Clos2ᵀ --CC: concretize--> Clos3ᵀ --CC: split--> Clos4ᵀ
          --CC: hoist--> Clos5ᵀ --rco--> Monᵀ --lift locals--> Impᵀ
          --explicate control--> CFGᵀ --select instructions--> X86ᵀ

(The passes marked "CC:" are the closure-conversion passes; the
languages marked ᵀ are intrinsically typed.)

The source, ISWIM, is untyped. Cast insertion, after *Essentials of
Compilation*, ch. 9, makes every check of the kind of a value explicit,
as a `project` from the type `Any` of tagged values; in the typed
languages after it, `project` is the only operation that can fail. The
target, X86ᵀ, is x86 with variables over abstract values, intrinsically
typed after Morrisett, Walker, Crary and Glew's TAL: its instructions
are typed by the types of the registers, the frame and the flag they
start and end with, and its only check is `project`'s (`chk`), which
stands for the X86 instruction that errs on a value of another kind.
Without its types, the code is that of x86 with variables (untyped X86),
which select emitted before (an assurance theorem,
`agda/Theorems/X86Erasure.agda`).

The first pass, simplify (ISWIM → ISWIM), is a source optimizer, a
simplified version of Chez Scheme's cp0: constant folding, case of a
known injection, projection from a known tuple, β on values (and on
`let`), and inlining of known functions (under fuel, when the result is
small); an operand that is not a value stays bound by a `let`.

The untyped pipeline that preceded this one (ISWIM → Clos2 → … → Clos5
→ Imp → CFG → X86, with untyped intermediate languages whose semantics
check kinds themselves) is preserved, with its proofs in the same five
styles, in `agda/Untyped/`; `make check` checks it too.

The public theorem statements are in `agda/Theorems/` (and
`agda/Untyped/Theorems/`); with the definitions they use (everything
outside the `proof/` directories) they are what must be read to trust
the results, and `agda/proof/` (and `agda/Untyped/proof/`) holds the
proofs. See `agda/README.md`.

It needs only the Agda standard library, and is checked with `--safe`
(so nothing postulated is used). From the root of the repository:

    make check

which runs `agda --safe agda/All.agda` and then greps the checked tree
for postulates and pragmas. This has been checked with Agda 2.8.0 and
version 2.4 of the standard library.

The parts of the abt library that it uses are in `agda/Framework/abt/`.

Line counts of the proofs, and their comparison, are in
`papers/PLDI-2027/loc.md` (`python3 papers/PLDI-2027/loc.py`, and
`--untyped` for the preserved pipeline).

The denotational: Scott domains column (`agda/AllScott.agda`,
`agda/Mu/Theorems/ScottDomains.agda`) also needs TypeTopology; check it with

    make check-scott

which clones TypeTopology at a pinned commit into `_deps/` (not tracked),
patches it, and checks the column against it and the standard library.

## Reproducing the PLDI 2027 paper

The paper's compiler (`agda/Mu/`) compiles FPC, Plotkin's Fixed Point
Calculus (a call-by-value λ-calculus with iso-recursive types), in ten
passes to X86μ.

* Graph model, abstract machines, clocked interpreters, reduction
  semantics, and adequacy: `make check` (Agda 2.8.0, standard library
  2.4, `--safe`; about three minutes). `agda/All.agda` imports
  `agda/Mu/All.agda`.
* Scott domains: `make check-scott`. It fetches TypeTopology at commit
  `17487fc910f3bb305c30001507fed5d41d52dc3c` into `_deps/`, applies
  `scott/typetopology-builtin-alias.patch` (Bool and List become
  aliases of Agda's builtins), and checks `agda/AllScott.agda` with
  `--safe` (about three more minutes). Its theorems take propositional
  truncation, function extensionality and propositional extensionality
  as module parameters.
* Theorem statements, one file per style, named as in the paper:
  `agda/Mu/Theorems/GraphModel.agda` (Theorems 4.1 and 4.4),
  `ScottDomains.agda` (Theorem F.4), `AbstractMachines.agda` (Theorem
  F.2), `ClockedInterpreters.agda` (Theorem F.1),
  `ReductionSemantics.agda` (Theorem F.3), and `Adequacy.agda` (Theorem
  4.5).
* `agda/Mu/README.md` maps each theorem, lemma, definition and appendix
  section of the paper to its Agda file and name, and lists the audit
  surface.
* Tables 1 and 2: `python3 papers/PLDI-2027/loc.py --mu` (the four
  columns, infrastructure and adequacy) and `--scott` (the Scott-domain
  column, its infrastructure and TypeTopology's); add `--tokens` or
  `--chars` for the other measures.

## Other developments

* `agda/old/` holds the earlier developments. They use the abt library
  (github.com/jsiek/abstract-binding-trees, at commit 1387c40). Check
  them from inside `agda/old/`, which has its own `.agda-lib`.
* `step-indexed/` uses the abt and sil libraries, and also has its own
  `.agda-lib`; check its files from inside `step-indexed/`.
