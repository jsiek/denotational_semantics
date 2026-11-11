# Artifact: compiler correctness in a graph model, and in four other styles

This artifact is the Agda mechanization behind the paper. It defines the
paper's compiler, from FPC to Instrμ in eight passes, and proves it
correct in five semantic styles: the graph model (the paper's main
result), Scott domains, abstract machines, clocked interpreters and
reduction semantics. It also proves the graph model adequate for the
clocked interpreters, the abstract machines and the reduction
semantics, and the Scott-domain semantics adequate for the clocked
interpreters (Proposition 5.1), and it measures the sizes of the five
proofs (Tables 1 and 2 of the paper).

    FPC --simplify--> FPC --capture--> Clos --prune--> Clos
           --concretize--> EnvClos --split--> PairClos
           --hoist--> GlobalFun --rco--> Mon --lift locals--> Imp
           --explicate control--> CFG --select instructions--> Instrμ

The paper's pass enclose is the three passes capture, prune and
concretize here, and the paper's target language Instrμ is `X86μ`
(`agda/FPC/Language/X86.agda`) in the Agda.

Every file is checked with `--safe`, and no file postulates anything.

## Contents

| Path | What |
|---|---|
| `agda/FPC/` | FPC: its languages, passes, semantics in the five styles, the theorem statements (`agda/FPC/Theorems/`) and the proofs (`agda/FPC/proof/`). [`agda/FPC/README.md`](agda/FPC/README.md) is the road map from the paper to the code. |
| `agda/Framework/`, `agda/proof/Framework/` | the language-independent infrastructure: abstract binding trees, the graph model (values, operators, continuity), the Scott domains on TypeTopology, the small-step, reduction and clocked frameworks |
| `agda/Language/`, `agda/Semantics/` | the primitives, the registers, the observations, and instances of the frameworks shared by the styles |
| `agda/FPC/All.agda` | the root of `make check`: everything but the Scott domains |
| `agda/AllScott.agda` | the root of `make check-scott`: the Scott domains and their adequacy |
| `vendor/TypeTopology/` | the subset of TypeTopology that the Scott domains import, patched (see its `NOTICE`) |
| `loc.py` | the script that measures Tables 1 and 2 (`make tables`) |
| `Makefile`, `Dockerfile`, `fpc-compiler.agda-lib` | the build |
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

## How long it takes

From scratch in Docker (no interface files, the standard library
included), on a desktop workstation (Intel Core Ultra 9 285K, 64 GB):

| Target | Time |
|---|---|
| `make check` | about 2 minutes |
| `make check-scott` (after `make check`) | about 6.5 minutes |
| `make tables` | under a second |
| `make all` | about 8.5 minutes |

## The paper's claims

Paths are relative to `agda/`. Each theorem of `FPC/Theorems/` has its
type written out and is defined as the corresponding theorem of
`FPC/proof/`, so Agda checks that the statement is the type of the
proof. [`agda/FPC/README.md`](agda/FPC/README.md) has the finer map (each
definition, figure and appendix section).

| Paper | Statement | Proof | Agda names |
|---|---|---|---|
| Lemma 3.1 (β) | | `proof/Framework/GraphModel/Ops.agda` | `Λ-β`, `ΛΛ-β` |
| Theorem 4.1 (Compiler correctness, graph model) | `FPC/Theorems/CorrectWrtGraphModel.agda` | `FPC/proof/Correctness/GraphModel/CompilerCorrect.agda` | `compile-int-const`, `compile-int-nonempty`; every type: `compile-correct-const`, `compile-correct-nonempty` |
| Theorem 4.2 (Compiler correctness, Scott domains) | `FPC/Theorems/CorrectWrtScottDomains.agda` | `FPC/proof/Correctness/ScottDomains/CompilerCorrect.agda` | `compile-int-const`, `compile-int-defined`; every type: `compile-correct-const`, `compile-correct-defined` |
| Lemma 4.3 (Passes proved by an equation) | | `FPC/proof/Correctness/GraphModel/<Pass>Correct.agda` | `simplify-correct`, `capture-correct`, `prune-correct`, `concretize-correct` (enclose: `enclose-correct`, in `CompilerCorrect.agda`), `hoist-correct`, `rco-correct`, `lift-locals-correct`, `explicate-correct`, `select-correct` |
| Lemma 4.4 (Depth irrelevance and unfolding) | | `FPC/proof/Correctness/GraphModel/ApproxLR.agda` | `ApproxLR-depth-irrelevant`; `unfold`, `fold` |
| Lemma 4.5 (Fundamental lemma) | | `FPC/proof/Correctness/GraphModel/SplitReflect.agda` | `split-reflect` |
| Lemma 4.6 (Correctness of split closure) | `FPC/Theorems/CorrectWrtGraphModel.agda` | `FPC/proof/Correctness/GraphModel/SplitCorrect.agda` (reflection: `SplitReflect.agda`; preservation: `SplitPreserve.agda`) | `split-correct-const`, `split-correct-nonempty` |
| §4.2, "Design alternatives: which sides to relate": a finite source side fails | | `FPC/proof/Correctness/GraphModel/SplitDesignFiniteSource.agda` | `no-finite-source-ApproxLR′`, `finite-source′`, `no-finite-source` |
| §4.2, "Design alternatives: which sides to relate": target sets of bounded depth | | `FPC/proof/Correctness/GraphModel/SplitDesignBoundedSets.agda` | `ApproxLRSet⇔` |
| Proposition 5.1 (Adequacy), graph model | `FPC/Theorems/GraphModelAdequateWrtClockedInterpreters.agda` | `FPC/proof/Adequacy/FPC.agda`, `FPC/proof/Adequacy/X86.agda` | `fpc-const-iff`, `fpc-diverges-iff`, `x86-const-iff`, `x86-diverges-iff` |
| Proposition 5.1, Scott domains | `FPC/Theorems/ScottDomainsAdequateWrtClockedInterpreters.agda` | `FPC/proof/Adequacy/ScottDomains/` | `fpc-const-iff`, `fpc-diverges-iff`, `x86-const-iff`, `x86-diverges-iff` |
| §5, the graph model and the abstract machines | `FPC/Theorems/GraphModelAdequateWrtAbstractMachines.agda` | `FPC/proof/Adequacy/AbstractMachines/` | `fpc-const-iff`, `fpc-diverges-iff`, `x86-const-iff`, `x86-diverges-iff` |
| §5, the graph model and the reduction semantics | `FPC/Theorems/GraphModelAdequateWrtReductionSemantics.agda` | `FPC/proof/Adequacy/ReductionSemantics/` | `fpc-const-iff`, `fpc-diverges-iff` |
| §5, Theorems 4.1 and 4.2 with Proposition 5.1 give the statements of Propositions F.1–F.3 | the four adequacy files above | `EndToEnd.agda` in each adequacy directory | `end-to-end-x86-const`, `end-to-end-x86-diverges` |
| Proposition F.1 (Correctness, clocked interpreters) | `FPC/Theorems/CorrectWrtClockedInterpreters.agda` | `FPC/proof/Correctness/ClockedInterpreters/CompilerFuel.agda` | `compile-const`, `compile-diverges`; every type: `compile-correct` |
| Proposition F.2 (Correctness, abstract machines) | `FPC/Theorems/CorrectWrtAbstractMachines.agda` | `FPC/proof/Correctness/AbstractMachines/PipelineSim.agda` | `compile-const`, `compile-diverges`; every type: `compile-correct` |
| Proposition F.3 (Correctness, reduction semantics) | `FPC/Theorems/CorrectWrtReductionSemantics.agda` | `FPC/proof/Correctness/ReductionSemantics/PipelineRed.agda` | `compile-const`, `compile-diverges`; every type: `compile-correct` |
| Lemmas G.1–G.5 (the Scott-domain proof of split closure) | | `FPC/proof/Correctness/ScottDomains/{SplitRel,SplitPreserve,SplitReflect,SplitTerms,SplitCorrect}.agda` | G.5: `split-correct-const`, `split-correct-defined` |
| Table 1 (lexical tokens of the five proofs) | | `../loc.py` | `make tables` |
| Table 2 (infrastructure) | | `../loc.py` | `make tables` |

The per-pass results of §4.1 and Appendix D (Lemma 4.3) are in
`FPC/proof/Correctness/GraphModel/<Pass>Correct.agda`, and those of the
other styles in `FPC/proof/Correctness/<style>/`; they are not restated
in `FPC/Theorems/`.

## Reproducing Tables 1 and 2

`make tables` runs `python3 loc.py --artifact`. The tables count the
lexical tokens of the code lines, and give each total in lines too
(`python3 loc.py --artifact --lines` prints them in lines). A code line is
a line that is not blank, not a comment and not part of an import
statement. The lexical tokens of a line are those of Agda's lexer,
approximately: its whitespace-separated words, split further at Agda's
delimiters, each of which is a token by itself (a parenthesis or brace,
`;`, `@`, and a `.` that starts a word). An identifier or operator, such
as `⟦_⟧₃`, `→` or `＝`, is one token when whitespace separates it. A
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
(`agda/FPC/Theorems/`) and the definitions they use, and nothing under a
`proof/` directory, which Agda has checked. No module outside a `proof/`
directory imports one inside it, except the theorem files, which cite
the proofs they re-export (`make tables` checks this). The surface is:

* the theorem statements: `FPC/Theorems/{CorrectWrtGraphModel,CorrectWrtAbstractMachines,CorrectWrtClockedInterpreters,CorrectWrtReductionSemantics,CorrectWrtScottDomains,GraphModelAdequateWrtClockedInterpreters,GraphModelAdequateWrtAbstractMachines,GraphModelAdequateWrtReductionSemantics,ScottDomainsAdequateWrtClockedInterpreters}.agda`;
* the languages and passes: `FPC/Language/*.agda`, `FPC/Compiler/*.agda`;
* heterogeneous vectors: `FPC/Framework/AllUtil.agda`, `FPC/Framework/ReductionAll.agda`;
* the graph model: `FPC/Semantics/GraphModel/{FPC,EnvClos,PairClos,Imp,CFG,X86,Ops,Closed}.agda`,
  `Framework/GraphModel/{Domain,SetsAsPredicates,Env,DOpSig,OpsBase,Ops}.agda`,
  `Semantics/Graph/Prim.agda`;
* Scott domains: `FPC/Semantics/ScottDomains/{FPC,Imp,CFG,X86,Ops,Closed}.agda`,
  `Framework/Scott/{Base,Sum,Lift,Functor,Solve,Domain,Ops,Semantics}.agda`,
  `Semantics/Scott/Prim.agda`;
* abstract machines: `FPC/Semantics/AbstractMachines/{FPC,GlobalFun,Imp,X86,Values}.agda`,
  `Framework/Smallstep.agda`, `Semantics/CEK/Smallstep.agda`;
* clocked interpreters: `FPC/Semantics/ClockedInterpreters/{FPC,GlobalFun,Imp,X86,Values}.agda`,
  `Framework/Clocked.agda`, `Semantics/Interp/Clock.agda`;
* reduction semantics: `FPC/Semantics/ReductionSemantics/FPC.agda`,
  `Framework/Reduction.agda`, `Semantics/Reduction/Smallstep.agda`
  (and the machine of Instrμ, above);
* shared: `Semantics/Observation.agda`, `Language/Prim.agda`,
  `Language/Reg.agda`, `Framework/{Primitives,Iff,Lookup,Membership}.agda`,
  `Framework/Syntax/Kit.agda`,
  `Framework/abt/{AbstractBindingTree,GSubst,ScopedTuple,Sig,Var}.agda`.

The example programs of `FPC/Examples.agda` are also outside `proof/`
and import no proof module: each states, and Agda checks by computation,
the result of a program on the interpreter of FPC. No theorem statement
uses them. The semantics of the other intermediate languages are used
only by the proofs.

## Assumptions

Every file is checked with `--safe`, and there are no postulates
(`make pragma-check`). The development uses axiom K (it is not checked
with `--without-K`, except the abstract-binding-tree extract). The
Scott-domain development, and so Theorem 4.2 and the Scott-domain half
of Proposition 5.1, takes three assumptions as module parameters of
`FPC/Theorems/CorrectWrtScottDomains.agda` and `FPC/Theorems/ScottDomainsAdequateWrtClockedInterpreters.agda`, those of
TypeTopology's domain theory: propositional truncation
(`pt : propositional-truncations-exist`), function extensionality
(`fe : Fun-Ext`) and propositional extensionality (`pe : propext 𝓤₀`).
The other styles assume nothing.

## What the artifact leaves out

The artifact is the import closure of `agda/FPC/All.agda` and
`agda/AllScott.agda`. The ISWIM pipeline (dynamically typed ISWIM, with
errors), which the paper reports only briefly, is not part of it.
Comments sometimes compare a module with its counterpart in that
pipeline (paths such as `ISWIM/proof/Correctness/Graph/...` or
`ISWIM/Semantics/CEK/Typed/...`); those files are not here, and nothing here
imports them. `loc.py` is the script that measures the whole
development, so it also defines the groups of modules of that pipeline;
with `--artifact` they are empty and skipped.
