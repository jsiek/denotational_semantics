# denotational_semantics
Denotational semantics based on graph and filter models

This repository has two Agda developments of a closure-converting
compiler, each proved correct in several semantic styles:

* **FPC** (`agda/FPC/`): a compiler for FPC, Plotkin's Fixed Point
  Calculus, a typed call-by-value λ-calculus with iso-recursive types.
  This is the development of the PLDI 2027 paper submission.
* **ISWIM** (`agda/ISWIM/`): a compiler for ISWIM, an untyped
  call-by-value λ-calculus.

The modules that the two share (the frameworks, the primitives, the
observations) are directly in `agda/`. `agda/README.md` describes the
layout of `agda/` in more detail.

## Checking

Both developments need only the Agda standard library (except FPC's
Scott-domain proofs, below), and are checked with `--safe`, so nothing
postulated is used. From the root of the repository:

    make check

runs `agda --safe agda/All.agda`, which imports both developments, and
then greps the checked tree for postulates and pragmas. This has been
checked with Agda 2.8.0 and version 2.4 of the standard library.

FPC's Scott-domain proofs (`agda/AllScott.agda`) also need TypeTopology;
check them with

    make check-scott

which clones TypeTopology at a pinned commit into `_deps/` (not tracked),
patches it, and checks the Scott-domain proofs against it and the
standard library. After that, `.dir-locals.el` makes Emacs's Agda mode
load files with the same libraries.

## The FPC development (PLDI 2027)

`agda/FPC/` compiles FPC in eight passes to Instrμ (`X86μ` in the Agda;
the paper's enclose pass is the Agda's capture, prune and concretize).
The source is intrinsically typed, with base types, tuples, sums and
iso-recursive types μX.A, and has no recursion construct and no errors.

    FPC --simplify--> FPC --capture--> Closμ --prune--> Closμ
           --concretize--> EnvClosμ --split--> PairClosμ
           --hoist--> GlobalFunμ --rco--> Monμ --lift locals--> Impμ
           --explicate control--> CFGμ --select instructions--> X86μ

The compiler is proved correct in five styles: the graph model (the
paper's main result), Scott domains, abstract machines (CEK machines
and simulations, after CompCert), clocked interpreters (with relations
on values, after CakeML), and reduction semantics (with simulations).
The graph model is proved adequate for the clocked interpreters, the
abstract machines and the reduction semantics, and the Scott-domain
semantics for the clocked interpreters.

* **Checking.** `make check` checks everything but the Scott-domain
  proofs. `make check-scott` checks those and their adequacy, in about
  six and a half more minutes. Their theorems take propositional
  truncation, function extensionality and propositional extensionality
  as module parameters.
* **Theorem statements**, one file per result, in `agda/FPC/Theorems/`:
  compiler correctness in `CorrectWrtGraphModel.agda` (Theorem 4.1 and
  Lemma 4.6), `CorrectWrtScottDomains.agda` (Theorem 4.2),
  `CorrectWrtClockedInterpreters.agda` (Proposition F.1),
  `CorrectWrtAbstractMachines.agda` (Proposition F.2) and
  `CorrectWrtReductionSemantics.agda` (Proposition F.3); adequacy
  (Proposition 5.1 and Section 5) in
  `GraphModelAdequateWrtClockedInterpreters.agda`,
  `GraphModelAdequateWrtAbstractMachines.agda`,
  `GraphModelAdequateWrtReductionSemantics.agda` and
  `ScottDomainsAdequateWrtClockedInterpreters.agda`.
* **Road map.** `agda/FPC/README.md` maps each theorem, lemma, definition
  and appendix section of the paper to its Agda file and name, lists the
  audit surface, and describes the example programs of
  `agda/FPC/Examples.agda`.
* **Tables 1 and 2** of the paper: `python3 papers/PLDI-2027/loc.py --mu`
  (the four columns, infrastructure and adequacy) and `--scott` (the
  Scott-domain column, its infrastructure and TypeTopology's); add
  `--tokens` or `--chars` for the other measures. `papers/PLDI-2027/loc.md`
  discusses the counts.
* **Artifact.** `make artifact` writes the anonymized artifact of the
  paper, which contains the FPC development and the shared modules,
  to `_artifact/` (see `artifact/export.py`).

## The ISWIM development

`agda/ISWIM/` (gathered by `agda/ISWIM/All.agda`) compiles ISWIM to
X86ᵀ, a typed assembly language, through intrinsically typed
intermediate languages (marked ᵀ):

    ISWIM --simplify--> ISWIM --cast insertion--> ISWIMᵀ --CC: capture--> Clos2ᵀ
          --CC: prune--> Clos2ᵀ --CC: concretize--> Clos3ᵀ --CC: split--> Clos4ᵀ
          --CC: hoist--> Clos5ᵀ --rco--> Monᵀ --lift locals--> Impᵀ
          --explicate control--> CFGᵀ --select instructions--> X86ᵀ

(The passes marked "CC:" are the closure-conversion passes.)

The first pass, simplify (ISWIM → ISWIM), is a source optimizer, a
simplified version of Chez Scheme's cp0: constant folding, case of a
known injection, projection from a known tuple, β on values (and on
`let`), and inlining of known functions (under fuel, when the result is
small); an operand that is not a value stays bound by a `let`.

The source is untyped. Cast insertion, after *Essentials of
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
`agda/ISWIM/Theorems/X86Erasure.agda`).

The compiler is proved correct in five styles: the graph model, CEK
machines with simulations, clocked interpreters with relations on
values, reduction semantics with simulations, and the graph model with
errors. The two graph models are proved adequate for the machines.

* **Theorem statements** are in `agda/ISWIM/Theorems/`; with the
  definitions they use (everything outside the `proof/` directories)
  they are what must be read to trust the results, and
  `agda/ISWIM/proof/` holds the proofs.
* **The untyped pipeline** that preceded this one (ISWIM → Clos2 → … →
  Clos5 → Imp → CFG → X86, with untyped intermediate languages whose
  semantics check kinds themselves) is preserved, with its proofs in the
  same five styles, in `agda/ISWIM/Untyped/` (statements in
  `agda/ISWIM/Untyped/Theorems/`); `make check` checks it too.
* **Line counts** of its proofs are in `papers/PLDI-2027/loc.md`
  (`python3 papers/PLDI-2027/loc.py`, and `--untyped` for the preserved
  pipeline).
* The parts of the abt library that it uses are in `agda/Framework/abt/`.

## Other developments

* `agda/old/` holds the earlier developments. They use the abt library
  (github.com/jsiek/abstract-binding-trees, at commit 1387c40). Check
  them from inside `agda/old/`, which has its own `.agda-lib`.
* `step-indexed/` uses the abt and sil libraries, and also has its own
  `.agda-lib`; check its files from inside `step-indexed/`.
