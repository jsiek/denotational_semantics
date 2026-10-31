# FPC: the Agda development of the PLDI 2027 paper

This directory is the mechanization behind the paper. It defines the
compiler of the paper, from FPC to x86μ in ten passes, and proves it
correct in five semantic styles. The styles are the graph model (the
paper's main result), Scott domains, abstract machines, clocked
interpreters, and reduction semantics. It also proves the graph model
adequate for the clocked interpreters. The source language is FPC
(Plotkin's Fixed Point Calculus), and `Mu` is for its iso-recursive
types: FPC is a call-by-value λ-calculus with base types, n-ary
tuples, sums and iso-recursive types μX.A, with no recursion construct
and no errors.

    FPC --simplify--> FPC --capture--> Closμ --prune--> Closμ
           --concretize--> EnvClosμ --split--> PairClosμ
           --hoist--> GlobalFunμ --rco--> Monμ --lift locals--> Impμ
           --explicate control--> CFGμ --select instructions--> X86μ

The Agda names carry a `μ` (`Closμ`, `X86μ`, ...) where the paper writes
Clos, x86μ, and so on. Paths below are relative to this directory
(`agda/Mu/`).

## Checking

From the repository root:

* `make check` checks the graph model, abstract machines, clocked
  interpreters, reduction semantics and adequacy (`../All.agda`, which
  imports [`All.agda`](All.agda)) with `--safe`, and then runs
  `make pragma-check`. It needs Agda 2.8.0 and the standard library
  2.4, and takes about three minutes.
* `make check-scott` checks the Scott-domain development
  (`../AllScott.agda`) with `--safe`. It needs TypeTopology, which
  `make scott-deps` fetches at a pinned commit into `_deps/` and patches
  (`../../scott/fetch-typetopology.sh`); `make check-scott` runs it
  first. It takes about three more minutes.
* `make pragma-check` fails if any checked file has a `postulate` or a
  pragma, other than the `--without-K` option of the abt extract.

[`Experiments.agda`](Experiments.agda) checks an experiment that is not
part of the paper (mixing semantics); `../All.agda` imports it too.

## Layout

* [`Theorems/`](Theorems/): the paper's theorems, one file per style.
  Each theorem has its type written out and is defined as the
  corresponding theorem of `proof/`, so Agda checks that the statement
  is the type of the proof.
* [`Language/`](Language/): the syntax and typing of each language
  (intrinsically typed: a term `Tm Γ A` is well typed by construction).
* [`Compiler/`](Compiler/): the passes, and their composition.
* [`Semantics/`](Semantics/): the semantics of each language in each
  style: `GraphModel/`, `ScottDomains/`, `AbstractMachines/`,
  `ClockedInterpreters/`, `ReductionSemantics/`.
* [`Framework/`](Framework/): heterogeneous vectors, which contexts,
  tuples and tables need.
* [`proof/`](proof/): all proofs. `proof/Correctness/<style>/` has one
  proof per pass and the composition, `proof/Semantics/<style>/` the
  lemmas about the semantics, and `proof/Adequacy/` adequacy. A module
  `X.agda` outside `proof/` keeps the definitions, and `proof/X.agda`,
  when it exists, re-exports them with their lemmas.

The language-independent definitions are shared with the other
pipelines of the repository and live in `../Framework/` (definitions)
and `../proof/Framework/` (lemmas): the graph model
(`../Framework/GraphModel/`), the Scott domains (`../Framework/Scott/`),
and the small-step, reduction and clocked frameworks.

## The paper's claims

| Paper | File | Agda name |
|---|---|---|
| Lemma 3.1 (β), part 1 | `../proof/Framework/GraphModel/Ops.agda` | `Λ-β` (Λ(F) • D is `letD`) |
| Lemma 3.1 (β), part 2 | `../proof/Framework/GraphModel/Ops.agda` | `ΛΛ-β` |
| Theorem 4.1 (Compiler correctness) | [`Theorems/GraphModel.agda`](Theorems/GraphModel.agda) | `compile-int-const`, `compile-int-nonempty`; every type: `compile-correct-const`, `compile-correct-nonempty` |
| Theorem 4.1, proof (composition of the passes) | `proof/Correctness/GraphModel/CompilerCorrect.agda` | `compile-int`, `compile-same` |
| Lemma 4.2 (Depth irrelevance and unfolding), part 1 | `proof/Correctness/GraphModel/ApproxLR.agda` | `ApproxLR-depth-irrelevant` (one direction; with k and j swapped, the other) |
| Lemma 4.2, part 2 | `proof/Correctness/GraphModel/ApproxLR.agda` | `unfold`, `fold` |
| monotone in D, antitone in V (after Lemma 4.2) | `proof/Correctness/GraphModel/ApproxLR.agda` | `ApproxLR-mono`, `ApproxLR-⊆` |
| Lemma 4.3 (Fundamental lemma) | `proof/Correctness/GraphModel/SplitReflect.agda` | `split-reflect` (related environments: `Envs`; the case of a call: `collect`; of a closure: `clos-app`) |
| Theorem 4.4 (Correctness of split closure) | [`Theorems/GraphModel.agda`](Theorems/GraphModel.agda) | `split-correct-const`, `split-correct-nonempty` |
| Theorem 4.4, proof | `proof/Correctness/GraphModel/SplitCorrect.agda` (reflection: `proof/Correctness/GraphModel/SplitReflect.agda`, `reflect-const`, `reflect-nonempty`; preservation: `proof/Correctness/GraphModel/SplitPreserve.agda`, `preserve-const`, `preserve-nonempty`) | `split-correct-const`, `split-correct-nonempty` |
| Theorem 4.5 (Adequacy) | [`Theorems/Adequacy.agda`](Theorems/Adequacy.agda) | FPC: `fpc-const-iff`, `fpc-diverges-iff`; x86μ: `x86-const-iff`, `x86-diverges-iff` |
| Theorem 4.5, proof | `proof/Adequacy/FPC.agda` (`const-iff`, `diverges-iff`), `proof/Adequacy/X86.agda` (`x86-const-iff`, `x86-diverges-iff`); soundness: `proof/Adequacy/Soundness.agda`, `proof/Adequacy/X86Soundness.agda`; the logical relations: `proof/Adequacy/LogRel.agda`, `proof/Adequacy/X86LogRel.agda` | |
| Theorems 4.1 and 4.5 together: the operational theorem (§4.3) | [`Theorems/Adequacy.agda`](Theorems/Adequacy.agda); proof `proof/Adequacy/EndToEnd.agda` | `end-to-end-x86-const`, `end-to-end-x86-diverges` |
| §4.2, "Which sides to relate": a finite source side fails the function clause (the Agda check) | `proof/Correctness/GraphModel/SplitDesignFiniteSource.agda` | example 3 of its header, the paper's (λf.f, the singletons of [n] ↦ n): `no-finite-source-ApproxLR′`, `finite-source′`; example 1: `no-finite-source-ApproxLR`; any such relation: `no-finite-source` |
| §4.2, "Which sides to relate": a target set of bounded depth is related exactly when each finite sublist is (the Agda check) | `proof/Correctness/GraphModel/SplitDesignBoundedSets.agda` | `ApproxLRSet⇔` (from `ApproxLRSet⇒`, `ApproxLRSet⇐`) |
| Theorem F.1 (Correctness, clocked interpreters) | [`Theorems/ClockedInterpreters.agda`](Theorems/ClockedInterpreters.agda); proof `proof/Correctness/ClockedInterpreters/CompilerFuel.agda` | `compile-const`, `compile-diverges`; every type: `compile-correct` |
| Theorem F.2 (Correctness, abstract machines) | [`Theorems/AbstractMachines.agda`](Theorems/AbstractMachines.agda); proof `proof/Correctness/AbstractMachines/PipelineSim.agda` | `compile-const`, `compile-diverges`; every type: `compile-correct` |
| Theorem F.3 (Correctness, reduction semantics) | [`Theorems/ReductionSemantics.agda`](Theorems/ReductionSemantics.agda); proof `proof/Correctness/ReductionSemantics/PipelineRed.agda` | `compile-const`, `compile-diverges`; every type: `compile-correct` |
| Theorem F.4 (Correctness, Scott domains) | [`Theorems/ScottDomains.agda`](Theorems/ScottDomains.agda); proof `proof/Correctness/ScottDomains/CompilerCorrect.agda` | `compile-int-const`, `compile-int-defined`; every type: `compile-correct-const`, `compile-correct-defined` |
| Table 1 (lines of the five proofs) | `../../papers/PLDI-2027/loc.py` | `python3 papers/PLDI-2027/loc.py --mu` (four columns), `--scott` (the Scott column) |
| Table 2 (infrastructure) | `../../papers/PLDI-2027/loc.py` | `--mu` (its infrastructure table), `--scott` (the Scott infrastructure and TypeTopology; needs `make scott-deps`) |

A closed term is `Tm [] A`; `base Int` is the type Int. In the graph
model, c ∈ D is `const c ∈ D`, D ≠ ∅ is `nonempty D`, and the empty
environment ρ₀ is `ρ₀` of `Semantics/GraphModel/Closed.agda`.

The per-pass results of §4.1 and Appendix D are proved in
`proof/Correctness/GraphModel/<Pass>Correct.agda` (`simplify-correct`,
`capture-correct`, `prune-correct`, `concretize-correct`,
`hoist-correct`, `rco-correct`, `lift-locals-correct`,
`explicate-correct`, `select-correct`), and those of the other styles
in `proof/Correctness/<style>/`. They are not restated in `Theorems/`.
The graph-model correctness of enclose, `enclose-correct`, composes
those of capture, prune and concretize in
`proof/Correctness/GraphModel/CompilerCorrect.agda`.

## The paper's definitions

### Languages (Figure 1, Section 2, Appendix B)

| Language | File | Agda |
|---|---|---|
| types and contexts | [`Language/Type.agda`](Language/Type.agda) | `Ty`, `Type`, `Ctx`, `_⇒_`, `_⊹_`, `tup`, `base`, `μ` types and `unroll` |
| FPC | [`Language/FPC.agda`](Language/FPC.agda) | `Tm` (renaming and substitution: `Language/FPCSubst.agda`) |
| Clos | [`Language/Clos.agda`](Language/Clos.agda) | `Tm` |
| EnvClos | [`Language/EnvClos.agda`](Language/EnvClos.agda) | `Tm` |
| PairClos | [`Language/PairClos.agda`](Language/PairClos.agda) | `Tm` |
| GlobalFun | [`Language/GlobalFun.agda`](Language/GlobalFun.agda) | `Tm`, `Code`, `Program`, `DSig` |
| Mon | [`Language/Mon.agda`](Language/Mon.agda) | `Atm`, `Exp`, `Program`; its embedding into GlobalFun, `⌜_⌝ₚ` (Mon has no semantics of its own) |
| Imp | [`Language/Imp.agda`](Language/Imp.agda) | `Simple`, `Exp`, `Program` |
| CFG | [`Language/CFG.agda`](Language/CFG.agda) | `Tail`, `Blocks`, `Body`, `Program` |
| x86μ | [`Language/X86.agda`](Language/X86.agda) | `RTy`, `Regs`, `St`, `Arg`, `Dst`, `Instr`, `Seq`, `Blocks`, `Body`, `Program` |

The primitives and their δ are `../Language/Prim.agda` (`Prim`, `δ`)
and the registers `../Language/Reg.agda`, shared with the other
pipelines.

### Passes (Section 2, Appendix C)

| Pass | File | Agda |
|---|---|---|
| simplify (FPC to FPC) | [`Compiler/Simplify.agda`](Compiler/Simplify.agda) | `simplify` |
| capture (FPC to Clos) | [`Compiler/Capture.agda`](Compiler/Capture.agda) | `capture` |
| prune (Clos to Clos) | [`Compiler/Prune.agda`](Compiler/Prune.agda) | `prune-program` |
| concretize (Clos to EnvClos) | [`Compiler/Concretize.agda`](Compiler/Concretize.agda) | `concretize-program` (`concretize` with references φ: `Ref`, `Refs`) |
| enclose (FPC to EnvClos), the closure-conversion pass: concretize ∘ prune ∘ capture | [`Compiler/Pipeline.agda`](Compiler/Pipeline.agda) | `enclose` |
| split closure (EnvClos to PairClos) | [`Compiler/Split.agda`](Compiler/Split.agda) | `split-program` (`split`) |
| hoist (PairClos to GlobalFun) | [`Compiler/Hoist.agda`](Compiler/Hoist.agda) | `hoist` |
| remove complex operands (GlobalFun to Mon) | [`Compiler/RCO.agda`](Compiler/RCO.agda) | `rco-program` |
| lift locals (Mon to Imp) | [`Compiler/LiftLocals.agda`](Compiler/LiftLocals.agda) | `lift-program` |
| explicate control (Imp to CFG) | [`Compiler/Explicate.agda`](Compiler/Explicate.agda) | `explicate` |
| select instructions (CFG to x86μ) | [`Compiler/Select.agda`](Compiler/Select.agda) | `select` (the frame's slots: `depth`) |
| the compiler, `compile` | [`Compiler/Pipeline.agda`](Compiler/Pipeline.agda) | `compile` (prefixes: `compile-to-PairClos`, `compile-to-GlobalFun`, `compile-to-Mon`, `compile-to-Imp`, `compile-to-CFG`) |

### Semantics, in each of the five styles

| Language | Graph model (Appendix B) | Scott domains (F.5) | Abstract machines (F.3) | Clocked interpreters (F.2) | Reduction semantics (F.4) |
|---|---|---|---|---|---|
| FPC | `Semantics/GraphModel/FPC.agda`: `⟦_⟧` | `Semantics/ScottDomains/FPC.agda`: `⟦_⟧` | `Semantics/AbstractMachines/FPC.agda`: `State`, `step`, `sem` | `Semantics/ClockedInterpreters/FPC.agda`: `eval`, `call`, `sem` | `Semantics/ReductionSemantics/FPC.agda`: `red`, `sem` |
| Clos | `Semantics/GraphModel/Clos.agda`: `⟦_⟧` | `Semantics/ScottDomains/Clos.agda`: `⟦_⟧` | `Semantics/AbstractMachines/Clos.agda`: `sem` | `Semantics/ClockedInterpreters/Clos.agda`: `eval`, `sem` | `Semantics/ReductionSemantics/Clos.agda`: `red`, `sem` |
| EnvClos | `Semantics/GraphModel/EnvClos.agda`: `⟦_⟧` | `Semantics/ScottDomains/EnvClos.agda`: `⟦_⟧` | `Semantics/AbstractMachines/EnvClos.agda`: `sem` | `Semantics/ClockedInterpreters/EnvClos.agda`: `eval`, `sem` | `Semantics/ReductionSemantics/EnvClos.agda`: `red`, `sem` |
| PairClos | `Semantics/GraphModel/PairClos.agda`: `⟦_⟧` | `Semantics/ScottDomains/PairClos.agda`: `⟦_⟧` | `Semantics/AbstractMachines/PairClos.agda`: `sem` | `Semantics/ClockedInterpreters/PairClos.agda`: `eval`, `sem` | `Semantics/ReductionSemantics/PairClos.agda`: `red`, `sem` |
| GlobalFun | `Semantics/GraphModel/GlobalFun.agda`: `⟦_⟧ₚ` | `Semantics/ScottDomains/GlobalFun.agda`: `⟦_⟧ₚ` | `Semantics/AbstractMachines/GlobalFun.agda`: `sem` | `Semantics/ClockedInterpreters/GlobalFun.agda`: `sem` | `Semantics/ReductionSemantics/GlobalFun.agda`: `sem` |
| Mon | as its embedding `⌜_⌝ₚ` into GlobalFun, in every style | | | | |
| Imp | `Semantics/GraphModel/Imp.agda`: `⟦_⟧ₚ` | `Semantics/ScottDomains/Imp.agda`: `⟦_⟧ₚ` | `Semantics/AbstractMachines/Imp.agda`: `sem` | `Semantics/ClockedInterpreters/Imp.agda`: `sem` | the abstract machine |
| CFG | `Semantics/GraphModel/CFG.agda`: `⟦_⟧ₚ` | `Semantics/ScottDomains/CFG.agda`: `⟦_⟧ₚ` | `Semantics/AbstractMachines/CFG.agda`: `sem` | `Semantics/ClockedInterpreters/CFG.agda`: `sem` | the abstract machine |
| x86μ | `Semantics/GraphModel/X86.agda`: `⟦_⟧ₜ` | `Semantics/ScottDomains/X86.agda`: `⟦_⟧ₜ` | `Semantics/AbstractMachines/X86.agda`: `State`, `sem` | `Semantics/ClockedInterpreters/X86.agda`: `run`, `sem` | the abstract machine |

Shared by a style's languages: the empty environment ρ₀
(`Semantics/GraphModel/Closed.agda`, `Semantics/ScottDomains/Closed.agda`:
`ρ₀`), the tables of definitions (`Semantics/GraphModel/Ops.agda`,
`Semantics/ScottDomains/Ops.agda`), and the values of the machines and
interpreters (`Semantics/AbstractMachines/Values.agda`,
`Semantics/ClockedInterpreters/Values.agda`: `Val`, `obs`). The
meaning of the primitives is `../Semantics/Graph/Prim.agda` (`primD`,
`out`) and `../Semantics/Scott/Prim.agda` (`primD`, `out`).

### The graph model (Section 3, Figure 2, Appendix A)

| Paper | File | Agda |
|---|---|---|
| elements u, v, w (Figure 2) | `../Framework/GraphModel/Domain.agda` | `Value`: `const`, `_↦_`, `ν`, `⦅_,_⦆`, `tup[_]_`, `left`, `right`, `⟨⟩` (and `ω`, used only by the other pipelines' errors) |
| sets of elements, D ⊆ E, D = E | `../Framework/GraphModel/SetsAsPredicates.agda` | `𝒫`, `_∈_`, `_⊆_`, `_≃_`, `nonempty` |
| D • E (application) | `../Framework/GraphModel/Ops.agda` | `⋆` (written `_●_` in `proof/Correctness/GraphModel/ApproxLR.agda`) |
| Λ(F) | `../Framework/GraphModel/Ops.agda` | `Λ` (the curried form of Lemma 3.1, part 2: `ΛΛ`, `../proof/Framework/GraphModel/Ops.agda`) |
| pair, car, cdr | `../Framework/GraphModel/Ops.agda` | `pair`, `car`, `cdr` |
| D ⊙ E (call a closure) | `Semantics/GraphModel/PairClos.agda` (the meaning of `callc`), `proof/Correctness/GraphModel/SplitRel.agda` | `⟦ callc L M ⟧`, `_⊙_` |
| 𝒯(D₁, …, Dₙ) | `../Framework/GraphModel/Ops.agda` | `𝒯` |
| inl, inr | `../Framework/GraphModel/Ops.agda` | `inl`, `inr` |
| π_t (t = tupᵢ, left, right) | `../Framework/GraphModel/Ops.agda`, `../proof/Framework/GraphModel/DomainUtilBase.agda` | `proj` (tupᵢ), `Untag` (any tag) |
| consistency u ∼ v, V ≈ V′ (Appendix A.1, Figure 5) | `../Framework/GraphModel/Domain.agda` | `_~_`, `_≈_` |
| con(D) (Appendix A.1) | `../proof/Framework/GraphModel/Domain.agda` | `Con` |
| depth (Appendix A.2) | `../proof/Framework/GraphModel/DomainUtilBase.agda` | `depth`, `depths` (bounded depth: `Bnd`) |
| further operators (Appendix A.3): 𝒞, guard, prim, out, δ | `../Framework/GraphModel/Ops.agda`, `../Framework/GraphModel/OpsBase.agda`, `../Semantics/Graph/Prim.agda`, `../Language/Prim.agda` | `𝒞`, `guard-n`, `strict`, `ℬ` (constants), `primD`, `out`, `δ` |
| finitary, monotone (Lemma 3.1) | `../proof/Framework/GraphModel/OpsBase.agda` | `Finitary`, `Mono₁` |

### The proof of split closure (Section 4.2, Figures 3 and 4)

| Paper | File | Agda |
|---|---|---|
| v ⊑ D′ and U ⊑* E′ (Figure 3) | `proof/Correctness/GraphModel/SplitPreserve.agda` | `_⊑_`, `_⊑*_`; preservation: `preserve` |
| usable entry U_a ↦ w ∈ V (Figure 4) | `proof/Correctness/GraphModel/ApproxLR.agda` | `UsableEntry` (constructor `usable-entry`) |
| args(V) and a batch of calls (Figure 4) | `proof/Correctness/GraphModel/ApproxLR.agda` | `Batch` (fields `results` and `args`) |
| D ≼ₖ V and D ≼ V (Figure 4) | `proof/Correctness/GraphModel/ApproxLR.agda` | `ApproxLR≤`, `ApproxLR` |
| its four clauses | `proof/Correctness/GraphModel/ApproxLR.agda` | `ApproxLRLayer`: `const-obs`, `nonempty-obs`, `app-obs`, `tag-obs` |
| D related to every finite V ⊆ D′ | `proof/Correctness/GraphModel/SplitRel.agda` | `Approx` |
| related environments (before Lemma 4.3) | `proof/Correctness/GraphModel/SplitReflect.agda` | `Envs` |

## The appendices and the Agda

| Appendix | What | Agda |
|---|---|---|
| A.1 Consistency | u ∼ v, V ≈ V′, con(D) | `../Framework/GraphModel/Domain.agda` (`_~_`, `_≈_`), `../proof/Framework/GraphModel/Domain.agda` (`Con`) |
| A.2 Depth | depth of an element and a list | `../proof/Framework/GraphModel/DomainUtilBase.agda` (`depth`, `depths`) |
| A.3 Further Operators | 𝒯(), prim, out, δ, 𝒞, guard | `../Framework/GraphModel/Ops.agda` (`𝒯`, `𝒞`, `guard-n`, `strict`), `../Framework/GraphModel/OpsBase.agda` (`ℬ`), `../Semantics/Graph/Prim.agda` (`primD`, `out`), `../Language/Prim.agda` (`δ`) |
| B (opening) | base types, ρ₀, ⟦M⟧ = ⟦M⟧ρ₀ | `Language/Type.agda`, `Semantics/GraphModel/Closed.agda` (`ρ₀`) |
| B.1 The FPC Language | typing, graph semantics | `Language/Type.agda`, `Language/FPC.agda`, `Semantics/GraphModel/FPC.agda` |
| B.2 The Clos and EnvClos Languages | typing, graph semantics | `Language/Clos.agda`, `Language/EnvClos.agda`, `Semantics/GraphModel/Clos.agda`, `Semantics/GraphModel/EnvClos.agda` |
| B.3 The PairClos Language | typing, graph semantics | `Language/PairClos.agda`, `Semantics/GraphModel/PairClos.agda` |
| B.4 The GlobalFun and Mon Languages | typing, graph semantics, the embedding of Mon | `Language/GlobalFun.agda`, `Language/Mon.agda` (`⌜_⌝ₚ`), `Semantics/GraphModel/GlobalFun.agda`, `Semantics/GraphModel/Ops.agda` (tables) |
| B.5 The Imp Language | typing, graph semantics | `Language/Imp.agda`, `Semantics/GraphModel/Imp.agda` |
| B.6 The CFG Language | typing, graph semantics | `Language/CFG.agda`, `Semantics/GraphModel/CFG.agda` |
| B.7 The x86μ Language | typing, graph semantics | `Language/X86.agda`, `Semantics/GraphModel/X86.agda` |
| C (opening) | the composition `compile` | `Compiler/Pipeline.agda` (`compile`) |
| C.1 simplify | | `Compiler/Simplify.agda` (`simplify`) |
| C.2 capture | | `Compiler/Capture.agda` (`capture`) |
| C.3 prune | | `Compiler/Prune.agda` (`prune-program`) |
| C.4 concretize | | `Compiler/Concretize.agda` (`concretize-program`) |
| C.5 split closure | | `Compiler/Split.agda` (`split-program`) |
| C.6 hoist | | `Compiler/Hoist.agda` (`hoist`) |
| C.7 remove complex operands | | `Compiler/RCO.agda` (`rco-program`) |
| C.8 lift locals | | `Compiler/LiftLocals.agda` (`lift-program`) |
| C.9 explicate control | | `Compiler/Explicate.agda` (`explicate`) |
| C.10 select instructions | | `Compiler/Select.agda` (`select`) |
| D, Capture | calculation | `proof/Correctness/GraphModel/CaptureCorrect.agda` (`capture-correct`) |
| D, Prune | calculation | `proof/Correctness/GraphModel/PruneCorrect.agda` (`prune-correct`) |
| D, Hoist | calculation | `proof/Correctness/GraphModel/HoistCorrect.agda` (`hoist-correct`) |
| D, Remove complex operands | calculation | `proof/Correctness/GraphModel/RCOCorrect.agda` (`rco-correct`) |
| D, Lift locals | calculation | `proof/Correctness/GraphModel/LiftLocalsCorrect.agda` (`lift-locals-correct`) |
| D, Explicate control | calculation | `proof/Correctness/GraphModel/ExplicateCorrect.agda` (`explicate-correct`) |
| E An Example of the Approximant Logical Relation | clause 3 on λy. x + y (the example itself is not mechanized) | `proof/Correctness/GraphModel/ApproxLR.agda` (`UsableEntry`, `Batch`, `ApproxLRLayer.app-obs`) |
| F.1 Values and Observations | values, obs, observations, machines, clocked interpreters, equivalence | `Semantics/AbstractMachines/Values.agda` and `Semantics/ClockedInterpreters/Values.agda` (`Val`, `obs`), `../Semantics/Observation.agda` (`Obs`), `../Framework/Smallstep.agda` (`Machine`, `Terminates`, `Diverges`, `Equivalent`), `../Framework/Clocked.agda` (`Result`, `Terminates`, `Diverges`, `Equivalent`) |
| F.2 Clocked Interpreters | FPC and x86μ; Theorem F.1 | `Semantics/ClockedInterpreters/FPC.agda`, `Semantics/ClockedInterpreters/X86.agda`; `Theorems/ClockedInterpreters.agda` |
| F.3 Abstract Machines | FPC and x86μ; Theorem F.2 | `Semantics/AbstractMachines/FPC.agda`, `Semantics/AbstractMachines/X86.agda`; `Theorems/AbstractMachines.agda` |
| F.4 Reduction Semantics | FPC; Theorem F.3 | `Semantics/ReductionSemantics/FPC.agda`, `../Framework/Reduction.agda` (`Red`, `step-in`); `Theorems/ReductionSemantics.agda` |
| F.5 Scott Domains | 𝔻, its operators, FPC and x86μ; Theorem F.4 | `../Framework/Scott/Domain.agda` (`Tag`, `Payload`, `𝔻`, `roll`, `unroll`, `defined`), `../Framework/Scott/Ops.agda` (`Λ`, `app`, `tuple`, `proj`, `pair`, `component`, `inl`, `inr`, `cases`, `seq`), `../Framework/Scott/Semantics.agda`, `../Semantics/Scott/Prim.agda`, `Semantics/ScottDomains/FPC.agda`, `Semantics/ScottDomains/X86.agda`, `Semantics/ScottDomains/Closed.agda` (`ρ₀`); `Theorems/ScottDomains.agda` |

The semantics of the intermediate languages in the four other styles,
which the paper leaves to the artifact, are in the table of semantics
above.

## The audit surface

To trust the theorem statements, a reviewer reads the theorem files and
the definitions they use, and nothing under `proof/`, which Agda has
checked. No module outside a `proof/` directory imports one inside it,
except the theorem files, which cite the proofs they re-export.
`python3 papers/PLDI-2027/loc.py --mu` checks this and prints the size
of each style's surface (the Scott column's is the closure of
`Theorems/ScottDomains.agda`, which needs TypeTopology). The surface is
the following 90 files (3470 lines of code, 2226 of them for the four
styles other than Scott domains):

* the theorem statements: `Theorems/GraphModel.agda`,
  `Theorems/AbstractMachines.agda`, `Theorems/ClockedInterpreters.agda`,
  `Theorems/ReductionSemantics.agda`, `Theorems/ScottDomains.agda`,
  `Theorems/Adequacy.agda`;
* the languages and passes: `Language/*.agda` (all eleven files),
  `Compiler/*.agda` (all eleven files);
* heterogeneous vectors: `Framework/AllUtil.agda`,
  `Framework/ReductionAll.agda`;
* the graph model: `Semantics/GraphModel/{FPC,EnvClos,PairClos,Imp,CFG,X86,Ops,Closed}.agda`,
  and `../Framework/GraphModel/{Domain,SetsAsPredicates,Env,DOpSig,OpsBase,Ops}.agda`,
  `../Semantics/Graph/Prim.agda`;
* Scott domains: `Semantics/ScottDomains/{FPC,Imp,CFG,X86,Ops,Closed}.agda`,
  `../Framework/Scott/{Base,Sum,Lift,Functor,Solve,Domain,Ops,Semantics}.agda`,
  `../Semantics/Scott/Prim.agda`;
* abstract machines: `Semantics/AbstractMachines/{FPC,GlobalFun,Imp,X86,Values}.agda`,
  `../Framework/Smallstep.agda`, `../Semantics/CEK/Smallstep.agda`;
* clocked interpreters: `Semantics/ClockedInterpreters/{FPC,GlobalFun,Imp,X86,Values}.agda`,
  `../Framework/Clocked.agda`, `../Semantics/Interp/Clock.agda`;
* reduction semantics: `Semantics/ReductionSemantics/FPC.agda`,
  `../Framework/Reduction.agda`, `../Semantics/Reduction/Smallstep.agda`
  (and the machine of x86μ, above);
* shared with the other pipelines: `../Semantics/Observation.agda`,
  `../Language/Prim.agda`, `../Language/Reg.agda`,
  `../Framework/{Primitives,Iff,Lookup,Membership}.agda`,
  `../Framework/Syntax/Kit.agda`,
  `../Framework/abt/{AbstractBindingTree,GSubst,ScopedTuple,Sig,Var}.agda`.

The semantics of the other intermediate languages
(`Semantics/<style>/{Clos,EnvClos,PairClos,GlobalFun}.agda` where not
listed above) are used only by the proofs, and are not on the surface.
Everything under `proof/` (here and in `../proof/`) is proof.

## Assumptions

Every file is checked with `--safe`, and there are no postulates
(`make pragma-check`). The development uses axiom K (it is not checked
with `--without-K`, except the abt extract). The Scott-domain
development, and so Theorem F.4, takes three assumptions as module
parameters of `Theorems/ScottDomains.agda`, those of TypeTopology's
domain theory: propositional truncation
(`pt : propositional-truncations-exist`), function extensionality
(`fe : Fun-Ext`) and propositional extensionality
(`pe : propext 𝓤₀`). The
other styles assume nothing.
