# The closure-conversion compiler and its correctness proofs

A compiler from ISWIM to X86,

    ISWIM --enclose--> Clos2 --optimize--> Clos2 --concretize--> Clos3
          --delay--> Clos4 --globalize--> Clos5 --rco--> Clos5
          --lift locals--> Imp --explicate control--> CFG
          --select instructions--> X86

proved correct four ways: denotational: graph model; CEK machine +
simulation (small-step machines and forward simulations, in the style of
CompCert); clocked interpreter + value relations (in the style of
CakeML); and reduction semantics + simulation (small-step reduction by
substitution, and forward simulations); and the graph model proved sound
and adequate for the machines.

A source optimizer, simplify (ISWIM → ISWIM, a simplified version of
Chez Scheme's cp0: constant folding, case of a known injection,
projection from a known tuple, β on values), runs before enclose but is
not yet part of the compiler; it is proved correct in two styles so far,
the graph model and the reduction semantics.

Check everything, from the root of the repository, with

    make check

which runs `agda --safe agda/All.agda` (no postulates, no unsafe flags,
standard library only) and then greps the checked tree (everything here
but `old/`) for `postulate`, `TERMINATING`, `NON_TERMINATING`,
`NO_TERMINATION_CHECK`, `NO_POSITIVITY_CHECK`, `NO_UNIVERSE_CHECK`,
`INJECTIVE`, `ETA`, `REWRITE` and `OPTIONS` flags other than
`--without-K`, failing if it finds any.

## The audit surface

Everything outside `proof/` is what must be read to trust the results:
the theorem statements and the definitions they use, and nothing else.
No module outside `proof/` imports one in `proof/`, except the theorem
files, which cite the proofs (`papers/PLDI-2027/loc.py` checks both, and
that every module outside `proof/` is used by a theorem statement).

* Theorem statements (`Theorems/`), each with its type written out and
  defined as the corresponding theorem of `proof/`:
  * `Theorems/Denotational.agda`: each pass (and simplify) preserves the
    meaning of a program in the graph model (delay: its constants and whether it has
    any), and the whole compiler, into Clos5, monadic Clos5, Imp, CFG and X86,
    preserves the constants a program produces and whether it produces
    anything.
  * `Theorems/Simulation.agda`: each pass, and the compiler into each of
    Clos5, monadic Clos5, Imp, CFG and X86, produces an equivalent
    machine (the same observations on termination, including going
    wrong, and divergence exactly when the source diverges).
  * `Theorems/Interpreter.agda`: the same, for the clocked interpreters.
  * `Theorems/Reduction.agda`: the same, for the reduction semantics of
    ISWIM and Clos2–Clos5 and the machines of Imp, CFG and X86, and for
    simplify (closed programs).
  * `Theorems/Adequacy.agda`: the graph model is sound and adequate for
    the ISWIM machine, and for the Clos5 and X86 machines running
    compiled programs; so the compiler, observed through the machines
    only, preserves the constants a closed program computes and whether
    it terminates with an answer.
* The compiler, shared by all four styles:
  * `Language/`: the languages (ISWIM, Clos2–Clos5, monadic normal
    form, Imp, CFG, X86) and the primitives.
  * `Compiler/`: the passes (and simplify, `Simplify.agda`, not yet
    composed) and their composition
    (`Pipeline.agda`: `compile`, `compile-mon`, `compile-imp`,
    `compile-cfg`, `compile-x86`), and the preconditions of the
    operational theorems: `Closed` (`EncloseScope.agda`) and `Scoped`
    (`PipelineScope.agda`).
  * `Framework/abt/`, `Framework/Syntax/`, `Framework/Primitives.agda`,
    `Framework/ListUtil.agda`: abstract binding trees, renaming,
    substitution, scoping (`WS`), the variables a term uses (`Uses`,
    `bound`), base types, and list lookups.
* The semantics, per style:
  * denotational: `Semantics/Graph/` (the meaning of the primitives,
    `Prim.agda`, and the semantics of each language) and
    `Framework/GraphModel/` (sets as predicates, environments, the
    values and their consistency, and the operators);
  * CEK machine + simulation: `Semantics/CEK/` (a small-step
    machine per language), `Semantics/CEK/Smallstep.agda` and
    `Framework/Smallstep.agda` (machines, termination, divergence,
    `Equivalent`), `Semantics/Observation.agda`;
  * clocked interpreter + value relations: `Semantics/Interp/` (a
    clocked interpreter per language), `Semantics/Interp/Clock.agda` and
    `Framework/Clocked.agda` (results, termination, divergence,
    `Equivalent`), `Semantics/Observation.agda`;
  * reduction semantics + simulation: `Semantics/Reduction/` (a reduction
    semantics by substitution for ISWIM and Clos2–Clos5, and
    `Semantics/Reduction/Smallstep.agda`), `Framework/Reduction.agda`
    (reductions as machines) and `Framework/Smallstep.agda`, and the machines of Imp, CFG
    and X86 (`Semantics/CEK/{Values,Imp,CFG,X86}.agda`),
    shared with the CEK machine + simulation style;
  * adequacy: those of the denotational and simulation theorems.

## `proof/`

The files in `proof/` have been checked by Agda, so you need not read
them to believe the results: it is enough that `make check` succeeds
(the theorem files then have the types they state, and nothing is
postulated or unsafe). You may of course want to read them to learn the
proof techniques.

`proof/` mirrors the paths of the surface: the lemmas about a module
`X` of the surface are in `proof/X.agda` (which re-exports `X`); the
correctness proofs of the passes are in `proof/Correctness/`, one
directory per style, and adequacy is in `proof/Adequacy/`:

* `proof/Correctness/Graph/`: the denotational proofs of
  the passes, and `proof/Semantics/Graph/`: the monotonicity,
  consistency and continuity of the semantics;
* `proof/Correctness/CEK/`: the forward simulations, and
  `proof/Semantics/CEK/`: the lemmas about runs of the machines;
* `proof/Correctness/Interp/`: the clock-for-clock proofs, and
  `proof/Semantics/Interp/Clock.agda`: clock-for-clock correctness at
  this compiler's observations;
* `proof/Correctness/Reduction/`: the forward simulations between
  reduction semantics (for simplify, `SimplifyRed.agda`, of the target by
  the source) (explicate control and select instructions are the
  CEK proofs, `proof/Correctness/CEK/{Explicate,Select}Sim.agda`,
  shared), and `proof/Semantics/Reduction/`: the values of each reduction
  semantics;
* `proof/Adequacy/`: soundness, adequacy, and the
  well-formedness of compiled programs;
* `proof/Framework/`: the language-independent lemmas (continuity of the
  operators, the generic denotational semantics and its monotonicity and
  continuity, renaming, substitution and relations closed under it,
  forward simulations, simulations between reduction semantics,
  clock-for-clock correctness);
* `proof/Compiler/`: syntactic facts about the passes (for simplify, its
  values, `Simplify.agda`), and examples;
* experiments, not part of the main results: a direct semantics of Imp
  (`proof/Semantics/Graph/ImpDirect.agda`) with lift locals and
  explicate control proved against it
  (`proof/Correctness/Graph/LiftLocalsCorrect.agda`,
  `proof/Correctness/Graph/ExplicateCorrect.agda`), and a direct
  backward simulation for delay (`proof/Semantics/CEK/Backward.agda`,
  `proof/Correctness/CEK/DelayBackSim.agda`).

The semantics of ISWIM and Clos2–Clos4 is defined on the surface
directly, as the fold of its operators over a term; `proof/` packages the
same operators as an instance of the generic `Semantics` record of
`proof/Framework/GraphModel/Semantics.agda`, whose `⟦_⟧` is that fold by
definition, together with their monotonicity. The theorem files check
that the two agree, as Agda accepts each statement only if its type is
definitionally that of the proof it cites.

`All.agda` imports the theorem files and every module of `proof/`, so
that `make check` checks everything. `old/` holds earlier developments,
not checked by `make check` (see the top-level README).

Line counts of the proofs, and of the audit surface, are in
`papers/PLDI-2027/loc.md` (`python3 papers/PLDI-2027/loc.py`).
