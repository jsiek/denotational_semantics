# denotational_semantics
Denotational semantics based on graph and filter models

## The closure-conversion compiler

`agda/All.agda` gathers a closure-conversion compiler, from ISWIM to
X86, and its correctness proofs, in three styles (a denotational graph
model, CompCert-style forward simulations, CakeML-style clocked
interpreters), with the adequacy of the graph model for the machines:

    ISWIM --enclose--> Clos2 --optimize--> Clos2 --concretize--> Clos3
          --delay--> Clos4 --globalize--> Clos5 --rco--> Clos5
          --lift locals--> Imp --explicate control--> CFG
          --select instructions--> X86

The public theorem statements are in `agda/Theorems/`; with the
definitions they use (everything outside `agda/proof/`) they are what
must be read to trust the results, and `agda/proof/` holds the proofs.
See `agda/README.md`.

It needs only the Agda standard library, and is checked with `--safe`
(so nothing postulated is used). From the root of the repository:

    make check

which runs `agda --safe agda/All.agda` and then greps the checked tree
for postulates and pragmas. This has been checked with Agda 2.8.0 and
version 2.4 of the standard library.

The parts of the abt library that it uses are in `agda/Framework/abt/`.

## Other developments

* `agda/old/` holds the earlier developments. They use the abt library
  (github.com/jsiek/abstract-binding-trees, at commit 1387c40). Check
  them from inside `agda/old/`, which has its own `.agda-lib`.
* `step-indexed/` uses the abt and sil libraries, and also has its own
  `.agda-lib`; check its files from inside `step-indexed/`.
