# Supplementary Material for *Denotational Results in Compiler Correctness and Comparisons with Operational Approaches*

The supplementary material includes: (1) the Agda code, (2) a script that
evaluates proof sizes, and (3) the Appendix.

**Agda code.** The main thing in the supplementary material is the Agda
mechanization behind the paper (`agda/`). This development defines the paper's
compiler, from FPC to Instrμ in eight passes. The development also proves the
compiler correct in five semantic styles: the graph model (the paper's main
result), Scott domains, abstract machines, clocked interpreters, and reduction
semantics. It also proves the graph model adequate for the clocked interpreters,
the abstract machines and the reduction semantics, and the Scott-domain
semantics adequate for the clocked interpreters.

    FPC --simplify--> FPC --capture--> Clos --prune--> Clos
           --concretize--> EnvClos --split--> PairClos
           --hoist--> GlobalFun --rco--> Mon --lift locals--> Imp
           --explicate control--> CFG --select instructions--> Instrμ

The paper's pass `enclose` is the three passes `capture`, `prune` and
`concretize` here. The paper's target language Instrμ is called `X86μ`
(`agda/FPC/Language/X86.agda`) in the Agda.

**Evaluation script.** The supplementary material also includes a script that
measures the sizes of the five proofs and generates data for Tables 1 and 2 of
the paper (`loc.py`).

**Appendix.** Finally, the supplementary material includes the Appendix that
supplements the main text (`Appendix.pdf`).

## Contents

| Path | Content |
|---|---|
| `agda/FPC/` | FPC: the (intermediate) languages, compiler passes, semantics in the five styles, the theorem statements (`agda/FPC/Theorems/`) and the proofs. [`agda/FPC/README.md`](agda/FPC/README.md) is the road map from the paper to the code. |
| `agda/Framework/`, `agda/proof/Framework/` | the language-independent infrastructure code |
| `agda/Language/`, `agda/Semantics/` | the primitives, the registers, the observations, and instances of the frameworks |
| `agda/FPC/All.agda` | the root of `make check`: everything but the Scott domains |
| `agda/AllScott.agda` | the root of `make check-scott`: the Scott domains and their adequacy |
| `vendor/TypeTopology/` | the subset of TypeTopology that the Scott domains import (see its `NOTICE`) |
| `loc.py` | the script that generates evaluation data for Tables 1 and 2 (`make tables`) |
| `Makefile`, `Dockerfile`, `fpc-compiler.agda-lib` | project build files |
| `.dir-locals.el` | for Agda's Emacs mode (see "Checking proofs interactively in Emacs") |
| `MANIFEST.sha256` | the SHA-256 checksum of every other file |

The paths in the paper's appendix ("Agda:" lines) are relative to `agda/`.

## Requirements

* Agda 2.8.0 and the Agda standard library 2.4 (the `Dockerfile` installs both),
  GNU make, and Python 3 (for collecting evaluation data and `make tables`).
* About 2 GB of memory (Agda's peak is about 1.9 GB).
* Network access for installing the Agda toolchain.

## Building with Docker

    docker build -t fpc-compiler .
    docker run --rm fpc-compiler                  # make all: check, check-scott, tables
    docker run --rm fpc-compiler make tables      # or any one target

The image pins Agda 2.8.0 (the official static Linux binary) and the
standard library 2.4, both by SHA-256. The run needs no network
(`docker run --rm --network none fpc-compiler` works).

## Building natively

With Agda 2.8.0 on the `PATH` and the standard library 2.4 registered
in Agda's libraries file (as `standard-library`), from this directory:

    make check          # graph model, machines, interpreters, reduction, adequacy
    make check-scott    # Scott domains and their adequacy, with the vendored TypeTopology
    make tables         # Tables 1 and 2
    make all            # the three

`make check` runs `agda --safe agda/FPC/All.agda` and then
`make pragma-check`, which fails if any file under `agda/` has a
`postulate` or a pragma, other than the `--without-K` option of the
abstract-binding-tree extract. `make check-scott` writes
`_build/libraries` (Agda's default libraries file plus
`vendor/TypeTopology/typetopology.agda-lib`) and runs
`agda --library-file=_build/libraries -l standard-library -l TypeTopology -i agda --safe agda/AllScott.agda`.
`make clean` removes Agda's interface files.

## Checking proofs interactively in Emacs

To load the files in Emacs, run `make libraries` (or `make check-scott`) first.
When opening files, Emacs asks whether to apply the directory's local variables
(`.dir-locals.el`). Please answer yes.
