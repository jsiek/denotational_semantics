# denotational_semantics
Denotational semantics based on graph and filter models

## The closure-conversion compiler

`agda/All.agda` gathers a closure-conversion compiler and its
correctness proofs, in the graph model:

    ISWIM --annotate--> Clos1 --enclose--> Clos2 --optimize--> Clos2
          --concretize--> Clos3 --delay--> Clos4

It needs only the Agda standard library, and is checked with `--safe`
(so nothing postulated is used). From the root of the repository:

    make check

which runs `agda --safe agda/All.agda`. This has been checked with
Agda 2.8.0 and version 2.4 of the standard library.

The parts of the abt library that it uses are in `agda/abt/`.

## Other developments

* `agda/old/` holds the earlier developments. They use the abt library
  (github.com/jsiek/abstract-binding-trees, at commit 1387c40). Check
  them from inside `agda/old/`, which has its own `.agda-lib`.
* `step-indexed/` uses the abt and sil libraries, and also has its own
  `.agda-lib`; check its files from inside `step-indexed/`.
