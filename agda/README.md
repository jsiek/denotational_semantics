# The closure-conversion compiler and its correctness proofs

A compiler from ISWIM to X86ᵀ, a typed assembly language,

    ISWIM --simplify--> ISWIM --cast insertion--> ISWIMᵀ --CC: enclose--> Clos2ᵀ
          --CC: optimize--> Clos2ᵀ --CC: concretize--> Clos3ᵀ --CC: delay--> Clos4ᵀ
          --CC: globalize--> Clos5ᵀ --rco--> Monᵀ --lift locals--> Impᵀ
          --explicate control--> CFGᵀ --select instructions--> X86ᵀ

(The passes marked "CC:" are the closure-conversion passes; the
languages marked ᵀ are intrinsically typed.)

proved correct five ways: denotational: graph model; CEK machine +
simulation (small-step machines and forward simulations, in the style of
CompCert); clocked interpreter + value relations (in the style of
CakeML); reduction semantics + simulation (small-step reduction by
substitution, and forward simulations); and the graph model with errors
(an error denotes a set holding ω, divergence ∅); with both graph models
proved sound and adequate for the machines.

The source, ISWIM, is untyped. Cast insertion (after *Essentials of
Compilation*, ch. 9) makes every check of the kind of a value explicit,
as a `project` from the type `Any` of tagged values, placed where the
ISWIM machine checks; the languages after it are intrinsically typed
(terms indexed by a context and a type), so `project` is the only
operation that can fail. The target, X86ᵀ (`Language/Typed/X86.agda`),
is a typed assembly language after Morrisett, Walker, Crary and Glew's
TAL: x86 with variables over abstract values, its instructions typed by
the machine states they start and end in (the types of the registers,
the frame, the open closure and the flag); its only check is
`project`'s, `chk`, which stands for the X86 instruction that errs on a
value of another kind and the move. Without the types it is untyped X86
(`Language/X86.agda`), the target of the untyped pipeline.

The first pass, simplify (ISWIM → ISWIM), is a source optimizer, a
simplified version of Chez Scheme's cp0: constant folding, case of a
known injection, projection from a known tuple, β on values (and on
`let`), and inlining of known functions (under fuel, when the result is
small); an operand that is not a value stays bound by a `let`.
Simplify removes function calls, so its interpreter proof is not clock
for clock: the simplified program needs no more clock than the original.

Check everything, from the root of the repository, with

    make check

which runs `agda --safe agda/All.agda` (no postulates, no unsafe flags,
standard library only) and then greps the checked tree (everything here
but `old/`, so `Untyped/` too) for `postulate`, `TERMINATING`,
`NON_TERMINATING`, `NO_TERMINATION_CHECK`, `NO_POSITIVITY_CHECK`,
`NO_UNIVERSE_CHECK`, `INJECTIVE`, `ETA`, `REWRITE` and `OPTIONS` flags
other than `--without-K`, failing if it finds any.

## Layout

* `Theorems/`: the public theorem statements (below).
* `Language/`: the untyped source ISWIM, untyped X86 (the untyped
  pipeline's target), and the primitives; `Language/Typed/`: the types
  (`Type.agda`: `Any`, the flat types, the tags `project` tests,
  `code n`), the typed languages ISWIMᵀ, Clos2ᵀ–Clos5ᵀ, Monᵀ, Impᵀ and
  CFGᵀ, and the target, X86ᵀ (`X86.agda`), with its erasure into X86
  (`X86Erase.agda`).
* `Compiler/`: the passes (simplify, cast insertion, enclose, optimize,
  concretize, delay, globalize, rco, lift locals, explicate control,
  select instructions, into X86ᵀ) and their compositions
  (`Pipeline.agda`: `compile₄`, `compile`, `compile-mon`, `compile-imp`,
  `compile-cfg`, `compile-x86`, which ends at X86ᵀ), `Closed`
  (`EncloseScope.agda`), the precondition of the theorems about the
  whole compiler, and select into untyped X86 (`SelectX86.agda`), not a
  pass but the code select emits without the types.
* `Semantics/<style>/`: the semantics of ISWIM in each style, and in
  `Semantics/<style>/Typed/` those of the typed languages, X86ᵀ among
  them (`<style>` is `Graph`, `CEK`, `Interp`, `Reduction` or
  `GraphErr`; the reduction semantics has none for the languages
  without binders, whose machines it shares with `CEK`);
  `Semantics/CEK/X86.agda`: the machine of untyped X86 (for the untyped
  pipeline, and for the typed one's assurance);
  `Semantics/Observation.agda`: the observations.
* `Framework/`: the language-independent infrastructure (abstract
  binding trees, syntax and substitution, typed indices and vectors, the
  graph model and its error monad, the semantics of intrinsically typed
  syntax, the small-step, reduction and clocked frameworks).
  `Framework/GraphModel/Prelude.agda` and `ErrorPrelude.agda` only
  re-export what every semantics in the graph model (with errors) opens:
  sets as predicates, DOp signatures, the domain, `Env`, `⋆` and `ℬ`
  (and the error monad); their `proof/` halves add the lemmas about
  them, for the proofs.  `papers/PLDI-2027/loc.py` looks through them.
* `proof/`: the proofs, mirroring the paths above (see below).
* `Untyped/`: the untyped pipeline that preceded this one, preserved
  and checked:

      ISWIM --simplify--> ISWIM --CC: enclose--> Clos2 --CC: optimize--> Clos2
            --CC: concretize--> Clos3 --CC: delay--> Clos4 --CC: globalize--> Clos5
            --rco--> Clos5 --lift locals--> Imp --explicate control--> CFG
            --select instructions--> X86

  `Untyped/` mirrors this directory: `Untyped/X.agda` (module
  `Untyped.X`) was `X.agda` before the typed pipeline became the main
  one (or, for X86's semantics in the graph models and the interpreter
  and its adequacy, before the typed pipeline came to end at X86ᵀ). It
  holds only what the untyped pipeline alone uses (its languages
  Clos2–Clos5, monadic Clos5, Imp and CFG, its passes, their semantics
  and proofs in every style, X86's semantics but its machine, its
  adequacy for Clos5 and X86, its theorem statements in
  `Untyped/Theorems/`, its examples and experiments); what both
  pipelines use (ISWIM, simplify and its proofs, the primitives, the
  observations, the ISWIM adequacy, the frameworks), and X86 and its
  machine, which the typed pipeline's assurance uses, stay here.
  `Untyped/All.agda` imports it, and `All.agda` imports that.

## The audit surface

Everything outside the `proof/` directories is what must be read to
trust the results: the theorem statements and the definitions they use,
and nothing else. No module outside a `proof/` directory imports one in
it, except the theorem files, which cite the proofs, and nothing outside
`Untyped/` imports a module of `Untyped/` (`papers/PLDI-2027/loc.py`
checks these, and that every module outside the `proof/` directories is
used by a theorem statement).

* Theorem statements (`Theorems/`), each with its type written out and
  defined as the corresponding theorem of `proof/`:
  * `Theorems/Denotational.agda`: each pass preserves the meaning of a
    program in the graph model (delay: its constants and whether it has
    any), and the whole compiler, into Clos5ᵀ, Monᵀ, Impᵀ, CFGᵀ and X86ᵀ,
    preserves the constants a closed program produces and whether it
    produces anything.
  * `Theorems/Simulation.agda`: each pass, and the compiler into each of
    Clos5ᵀ, Monᵀ, Impᵀ, CFGᵀ and X86ᵀ, produces an equivalent machine
    (the same observations on termination, including an error, and
    divergence exactly when the source diverges).
  * `Theorems/Interpreter.agda`: the same, for the clocked interpreters.
  * `Theorems/Reduction.agda`: the same, for the reduction semantics of
    ISWIM, ISWIMᵀ and Clos2ᵀ–Clos5ᵀ and the machines of Impᵀ, CFGᵀ and
    X86ᵀ.
  * `Theorems/Adequacy.agda`: the graph model is sound and adequate for
    the ISWIM machine, and for the Clos5ᵀ and X86ᵀ machines running
    compiled programs; so the compiler, observed through the machines
    only, preserves the constants a closed program computes and whether
    it terminates with an answer.
  * `Theorems/GraphErrors.agda`: in the graph model with errors every
    pass but delay preserves the meaning of a program, delay preserves
    and reflects errors, constants and values (`Same`), and so does the
    whole compiler; the model is adequate for the ISWIM and X86ᵀ
    machines on all three outcomes, and for the Clos5ᵀ machine by the
    CEK column's simulation; so the ISWIM machine on a closed program
    and the Clos5ᵀ and X86ᵀ machines on its compilation stop with an
    error together, stop with the same constants, stop with an answer
    together, and diverge together.
  * `Theorems/X86Erasure.agda` (assurance, not part of the comparison):
    without its types, the X86ᵀ code select emits is the X86 code of
    select into untyped X86 (`Compiler/SelectX86.agda`).
  * `Untyped/Theorems/`: the same six files for the untyped pipeline.
* The definitions they use: `Language/`, `Compiler/`, `Semantics/`,
  `Framework/` (see the layout above), and those of `Untyped/` outside
  `Untyped/proof/` for the untyped statements. Per style:
  * denotational: `Semantics/Graph/` (the meaning of the primitives,
    `Prim.agda`, ISWIM, and `Typed/`) and
    `Framework/GraphModel/` (sets as predicates, environments, the
    values and their consistency, the operators, the guard of `project`);
  * graph model with errors: `Semantics/GraphErr/` and
    `Framework/GraphModel/ErrorMonad.agda` (an error monad on 𝒫 Value,
    and the operators built from it over the graph model's);
  * CEK machine + simulation: `Semantics/CEK/` (a small-step machine
    per language), `Semantics/CEK/Smallstep.agda` and
    `Framework/Smallstep.agda` (machines, termination, divergence,
    `Equivalent`), `Semantics/Observation.agda`;
  * clocked interpreter + value relations: `Semantics/Interp/` (a
    clocked interpreter per language), `Semantics/Interp/Clock.agda` and
    `Framework/Clocked.agda` (results, termination, divergence,
    `Equivalent`);
  * reduction semantics + simulation: `Semantics/Reduction/` (a
    reduction semantics by substitution for ISWIM, ISWIMᵀ and
    Clos2ᵀ–Clos5ᵀ), `Framework/Reduction.agda` (reductions as machines)
    and `Framework/Smallstep.agda`, and the machines of Clos5ᵀ (its
    values), Impᵀ, CFGᵀ and X86ᵀ (`Semantics/CEK/Typed/{Clos5,Imp,CFG,X86}.agda`),
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

* `proof/Correctness/Graph/`: the denotational proofs of the passes, and
  `proof/Semantics/Graph/`: the monotonicity, consistency and continuity
  of the semantics;
* `proof/Correctness/CEK/`: the forward simulations (for simplify,
  `SimplifySim.agda`, of the target by the source, which may stutter;
  the whole compiler, `PipelineSim.agda`), and `proof/Semantics/CEK/`:
  the lemmas about runs of the machines;
* `proof/Correctness/Interp/`: the clock-for-clock proofs (for
  simplify, `SimplifyFuel.agda`, clock-monotone instead: `clocked-le`,
  `proof/Framework/Clocked.agda`), and `proof/Semantics/Interp/`:
  clock-for-clock correctness at this compiler's observations and the
  relation between typed values;
* `proof/Correctness/Reduction/`: the forward simulations between
  reduction semantics (for simplify, `SimplifyRed.agda`, of the target by
  the source; explicate control and select instructions are the CEK
  proofs, `proof/Correctness/CEK/{Explicate,Select}Sim.agda`, shared),
  and `proof/Semantics/Reduction/`: the values of each reduction
  semantics;
* `proof/Correctness/GraphErr/`, `proof/Semantics/GraphErr/` and
  `proof/Adequacy/GraphErr/`: the graph model with errors (X86ᵀ adequacy
  direct; Clos5ᵀ adequacy derived from `PipelineSim`,
  `Adequacy/GraphErr/EndToEnd.agda`);
* `proof/Adequacy/`: soundness and adequacy (the ISWIM ones are those of
  the untyped pipeline too);
* `proof/Framework/`: the language-independent lemmas (continuity of the
  operators, the generic denotational semantics and its monotonicity and
  continuity, the semantics of intrinsically typed syntax, renaming,
  substitution and relations closed under it, forward simulations,
  simulations between reduction semantics, clock-for-clock correctness);
* `proof/Compiler/`: syntactic facts about the passes (for simplify, the
  values and known values it inspects, `SimplifyFacts.agda`, used by its
  proofs, and that it keeps programs closed, `SimplifyScope.agda`; cast
  insertion on closed programs, `CastScope.agda`; globalize's references
  to older definitions, `GlobalizeOlder.agda`; that select emits, without
  the types, the code of select into untyped X86, `SelectErase.agda`),
  and examples (`Examples/`: smoke tests run by `refl`);
* `Untyped/proof/`: the same for the untyped pipeline, with its
  experiments: a direct semantics of Imp with lift locals and explicate
  control proved against it, and a direct backward simulation for delay.

`All.agda` imports the theorem files, every module of `proof/`, and
`Untyped/All.agda`, so that `make check` checks everything. `old/` holds
earlier developments, not checked by `make check` (see the top-level
README).

Line counts of the proofs, and of the audit surface, are in
`papers/PLDI-2027/loc.md` (`python3 papers/PLDI-2027/loc.py`, and
`--untyped` for the preserved pipeline).
