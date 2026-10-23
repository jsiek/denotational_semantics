# Artifact: compiler correctness in a graph model, and in four other styles

This artifact is the Agda mechanization behind the paper. It defines the
paper's compiler, from ISWIMμ to x86μ in ten passes, and proves it
correct in five semantic styles: the graph model (the paper's main
result), Scott domains, abstract machines, clocked interpreters and
reduction semantics. It also proves the graph model adequate for the
clocked interpreters of ISWIMμ and x86μ, and it measures the sizes of
the five proofs (Tables 1 and 2 of the paper).

    ISWIMμ --simplify--> ISWIMμ --enclose--> Clos --optimize--> Clos
           --concretize--> EnvClos --delay--> FlatClos
           --globalize--> GlobalFun --rco--> Mon --lift locals--> Imp
           --explicate control--> CFG --select instructions--> x86μ

Every file is checked with `--safe`, and no file postulates anything.

## Contents

| Path | What |
|---|---|
| `agda/Mu/` | ISWIMμ: its languages, passes, semantics in the five styles, the theorem statements (`agda/Mu/Theorems/`) and the proofs (`agda/Mu/proof/`). [`agda/Mu/README.md`](agda/Mu/README.md) is the road map from the paper to the code. |
| `agda/Framework/`, `agda/proof/Framework/` | the language-independent infrastructure: abstract binding trees, the graph model (values, operators, continuity), the Scott domains on TypeTopology, the small-step, reduction and clocked frameworks |
| `agda/Language/`, `agda/Semantics/` | the primitives, the registers, the observations, and instances of the frameworks shared by the styles |
| `agda/Mu/All.agda` | the root of `make check`: everything but the Scott domains |
| `agda/AllScott.agda` | the root of `make check-scott`: the Scott domains |
| `vendor/TypeTopology/` | the subset of TypeTopology that the Scott domains import, patched (see its `NOTICE`) |
| `loc.py` | the script that measures Tables 1 and 2 (`make tables`) |
| `Makefile`, `Dockerfile`, `iswim-mu.agda-lib` | the build |
| `MANIFEST.sha256` | the SHA-256 of every other file |

The paths in the paper's appendix ("Agda:" lines) are relative to
`agda/`.

## Requirements

* Agda 2.8.0 and the Agda standard library 2.4 (the `Dockerfile`
  installs both), GNU make, and Python 3 (for `make tables` only).
* About 2 GB of memory (Agda's peak is about 1.9 GB).
* No network access, other than for installing the toolchain:
  TypeTopology is vendored.

## Building with Docker

    docker build -t iswim-mu .
    docker run --rm iswim-mu                  # make all: check, check-scott, tables
    docker run --rm iswim-mu make tables      # or any one target

The image pins Agda 2.8.0 (the official static Linux binary) and the
standard library 2.4, both by SHA-256. The run needs no network
(`docker run --rm --network none iswim-mu` works).

## Building natively

With Agda 2.8.0 on the `PATH` and the standard library 2.4 registered
in Agda's libraries file (as `standard-library`), from this directory:

    make check          # graph model, machines, interpreters, reduction, adequacy
    make check-scott    # Scott domains, with the vendored TypeTopology
    make tables         # Tables 1 and 2
    make all            # the three

`make check` runs `agda --safe agda/Mu/All.agda` and then
`make pragma-check`, which fails if any file under `agda/` has a
`postulate` or a pragma, other than the `--without-K` option of the
abstract-binding-tree extract. `make check-scott` writes
`_build/libraries` (Agda's default libraries file plus
`vendor/TypeTopology/typetopology.agda-lib`) and runs
`agda --library-file=_build/libraries -l standard-library -l TypeTopology -i agda --safe agda/AllScott.agda`.
`make clean` removes Agda's interface files.

## How long it takes

From scratch in Docker (no interface files, the standard library
included), on a recent x86-64 laptop:

| Target | Time |
|---|---|
| `make check` | about 2 minutes |
| `make check-scott` (after `make check`) | about 2.5 minutes |
| `make tables` | under a second |
| `make all` | about 4 minutes |

## The paper's claims

Paths are relative to `agda/`. Each theorem of `Mu/Theorems/` has its
type written out and is defined as the corresponding theorem of
`Mu/proof/`, so Agda checks that the statement is the type of the
proof. [`agda/Mu/README.md`](agda/Mu/README.md) has the finer map (each
definition, figure and appendix section).

| Paper | Statement | Proof | Agda names |
|---|---|---|---|
| Lemma 3.1 (β) | | `proof/Framework/GraphModel/Ops.agda` | `Λ-β`, `ΛΛ-β` |
| Theorem 4.1 (Compiler correctness, graph model) | `Mu/Theorems/GraphModel.agda` | `Mu/proof/Correctness/GraphModel/CompilerCorrect.agda` | `compile-int-const`, `compile-int-nonempty`; every type: `compile-correct-const`, `compile-correct-nonempty` |
| Lemma 4.2 (Depth irrelevance and unfolding) | | `Mu/proof/Correctness/GraphModel/ApproxLR.agda` | `ApproxLR-depth-irrelevant`; `unfold`, `fold` |
| Lemma 4.3 (Fundamental lemma) | | `Mu/proof/Correctness/GraphModel/DelayReflect.agda` | `delay-reflect` |
| Theorem 4.4 (Correctness of delay) | `Mu/Theorems/GraphModel.agda` | `Mu/proof/Correctness/GraphModel/DelayCorrect.agda` (reflection: `DelayReflect.agda`; preservation: `DelayPreserve.agda`) | `delay-correct-const`, `delay-correct-nonempty` |
| Theorem 4.5 (Adequacy) | `Mu/Theorems/Adequacy.agda` | `Mu/proof/Adequacy/ISWIM.agda`, `Mu/proof/Adequacy/X86.agda` | `iswim-const-iff`, `iswim-diverges-iff`, `x86-const-iff`, `x86-diverges-iff` |
| Theorems 4.1 and 4.5 together (§4.3) | `Mu/Theorems/Adequacy.agda` | `Mu/proof/Adequacy/EndToEnd.agda` | `end-to-end-x86-const`, `end-to-end-x86-diverges` |
| §4.2, "Which sides to relate": a finite source side fails | | `Mu/proof/Correctness/GraphModel/DelayDesignFiniteSource.agda` | `no-finite-source-ApproxLR′`, `finite-source′`, `no-finite-source` |
| §4.2, "Which sides to relate": target sets of bounded depth | | `Mu/proof/Correctness/GraphModel/DelayDesignBoundedSets.agda` | `ApproxLRSet⇔` |
| Theorem F.1 (Correctness, clocked interpreters) | `Mu/Theorems/ClockedInterpreters.agda` | `Mu/proof/Correctness/ClockedInterpreters/CompilerFuel.agda` | `compile-const`, `compile-diverges`; every type: `compile-correct` |
| Theorem F.2 (Correctness, abstract machines) | `Mu/Theorems/AbstractMachines.agda` | `Mu/proof/Correctness/AbstractMachines/PipelineSim.agda` | `compile-const`, `compile-diverges`; every type: `compile-correct` |
| Theorem F.3 (Correctness, reduction semantics) | `Mu/Theorems/ReductionSemantics.agda` | `Mu/proof/Correctness/ReductionSemantics/PipelineRed.agda` | `compile-const`, `compile-diverges`; every type: `compile-correct` |
| Theorem F.4 (Correctness, Scott domains) | `Mu/Theorems/ScottDomains.agda` | `Mu/proof/Correctness/ScottDomains/CompilerCorrect.agda` | `compile-int-const`, `compile-int-defined`; every type: `compile-correct-const`, `compile-correct-defined` |
| Table 1 (lines of the five proofs) | | `../loc.py` | `make tables` |
| Table 2 (infrastructure) | | `../loc.py` | `make tables` |

The per-pass results of §4.1 and Appendix D are in
`Mu/proof/Correctness/GraphModel/<Pass>Correct.agda`, and those of the
other styles in `Mu/proof/Correctness/<style>/`; they are not restated
in `Mu/Theorems/`.

## Reproducing Tables 1 and 2

`make tables` runs `python3 loc.py --artifact`. A code line is a line
that is not blank, not a comment and not part of an import statement. A
proof's total is its own modules plus the shared modules it reaches
through imports that not all four of the graph model, machines,
interpreters and reduction semantics reach; the languages and passes,
which all four reach, are counted in no total. The infrastructure
(Table 2) is counted separately, for each proof the modules it reaches.
The script also checks the structure of the development: every module
belongs to exactly one group, no proof reaches another proof's modules,
and no module of the audit surface imports a proof module. Its output:

TABLES_OUTPUT

The script on the full development (`loc.py --tables`) prints the same
two tables.

## The audit surface

To trust the theorem statements, a reader reads the theorem files
(`agda/Mu/Theorems/`) and the definitions they use, and nothing under a
`proof/` directory, which Agda has checked. No module outside a `proof/`
directory imports one inside it, except the theorem files, which cite
the proofs they re-export (`make tables` checks this). The surface is:

* the theorem statements: `Mu/Theorems/{GraphModel,AbstractMachines,ClockedInterpreters,ReductionSemantics,ScottDomains,Adequacy}.agda`;
* the languages and passes: `Mu/Language/*.agda`, `Mu/Compiler/*.agda`;
* heterogeneous vectors: `Mu/Framework/AllUtil.agda`, `Mu/Framework/ReductionAll.agda`;
* the graph model: `Mu/Semantics/GraphModel/{ISWIM,EnvClos,FlatClos,Imp,CFG,X86,Ops,Closed}.agda`,
  `Framework/GraphModel/{Domain,SetsAsPredicates,Env,DOpSig,OpsBase,Ops}.agda`,
  `Semantics/Graph/Prim.agda`;
* Scott domains: `Mu/Semantics/ScottDomains/{ISWIM,Imp,CFG,X86,Ops,Closed}.agda`,
  `Framework/Scott/{Base,Sum,Lift,Functor,Solve,Domain,Ops,Semantics}.agda`,
  `Semantics/Scott/Prim.agda`;
* abstract machines: `Mu/Semantics/AbstractMachines/{ISWIM,GlobalFun,Imp,X86,Values}.agda`,
  `Framework/Smallstep.agda`, `Semantics/CEK/Smallstep.agda`;
* clocked interpreters: `Mu/Semantics/ClockedInterpreters/{ISWIM,GlobalFun,Imp,X86,Values}.agda`,
  `Framework/Clocked.agda`, `Semantics/Interp/Clock.agda`;
* reduction semantics: `Mu/Semantics/ReductionSemantics/ISWIM.agda`,
  `Framework/Reduction.agda`, `Semantics/Reduction/Smallstep.agda`
  (and the machine of x86μ, above);
* shared: `Semantics/Observation.agda`, `Language/Prim.agda`,
  `Language/Reg.agda`, `Framework/{Primitives,Iff,Lookup,Membership}.agda`,
  `Framework/Syntax/Kit.agda`,
  `Framework/abt/{AbstractBindingTree,GSubst,ScopedTuple,Sig,Var}.agda`.

The semantics of the other intermediate languages are used only by the
proofs.

## Assumptions

Every file is checked with `--safe`, and there are no postulates
(`make pragma-check`). The development uses axiom K (it is not checked
with `--without-K`, except the abstract-binding-tree extract). The
Scott-domain development, and so Theorem F.4, takes three assumptions as
module parameters of `Mu/Theorems/ScottDomains.agda`, those of
TypeTopology's domain theory: propositional truncation
(`pt : propositional-truncations-exist`), function extensionality
(`fe : Fun-Ext`) and propositional extensionality (`pe : propext 𝓤₀`).
The other styles assume nothing.

## What the artifact leaves out

The artifact is the import closure of `agda/Mu/All.agda` and
`agda/AllScott.agda`. The ISWIM pipeline (dynamically typed ISWIM, with
errors), which the paper reports only briefly, is not part of it.
Comments sometimes compare a module with its counterpart in that
pipeline (paths such as `proof/Correctness/Graph/...` or
`Semantics/CEK/Typed/...`); those files are not here, and nothing here
imports them. `loc.py` is the script that measures the whole
development, so it also defines the groups of modules of that pipeline;
with `--artifact` they are empty and skipped.
