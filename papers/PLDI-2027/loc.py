#!/usr/bin/env python3
"""Count code lines of the five compiler-correctness proofs, and of the
audit surface.

Run from the repository root:  python3 papers/PLDI-2027/loc.py
For the untyped pipeline preserved in agda/Untyped/:  ... loc.py --untyped
For the ISWIMμ pilot in agda/Mu/:  ... loc.py --mu

A code line is a line that is not blank, not a comment ({- -} blocks,
-- line comments) and not part of an import statement (`import` or
`open import`, with its continuation lines): imports depend on how
finely a development is split into modules, not on its content.  Every
.agda file under agda/ (except agda/old/ and the two All.agda) must
belong to exactly one group; the script fails otherwise, so new modules
cannot go uncounted.

Two pipelines.  The main one (the default) is the typed pipeline:
ISWIM --simplify--> ISWIM --cast insertion--> ISWIMᵀ --enclose--> ...
--select--> X86ᵀ, with intrinsically typed intermediate languages and an
intrinsically typed assembly language, X86ᵀ, as the target.  The
untyped pipeline that preceded it is preserved in agda/Untyped/ (module
prefix Untyped.); --untyped prints its tables, and the default output
ends with a table that compares the two, column by column.  Each column
of a pipeline is a side ('den', 'op', 'ck', 'red', 'gerr' for the typed
one; 'uden', 'uop', 'uck', 'ured', 'ugerr' for the untyped one), and so
are their adequacy proofs ('adeq', 'gadeq'; 'uadeq', 'ugadeq').  What
both pipelines use (untyped ISWIM and simplify with its proofs, the
primitives, the observations, the ISWIM adequacy) stays in agda/ and
belongs to groups of both sides ('den+uden'): it is counted in full in
that row of both pipelines.  Untyped X86 (Language/X86.agda) and its
CEK machine stay in agda/ too, for the untyped pipeline and for the
typed one's assurance (below); its other semantics and its adequacy are
the untyped pipeline's, in agda/Untyped/.

Assurance (side 'assure', not in any total nor in the comparison):
checks that the typed pipeline's X86ᵀ is faithful to untyped X86, such
as that erasing X86ᵀ to X86 keeps the meaning of every program, and that
select, with the types erased, emits the instructions of select into
untyped X86 (Theorems/X86Erasure.agda).

The code is split into an audit surface (the theorem statements,
agda/Theorems/ and agda/Untyped/Theorems/, and the definitions they use,
everywhere outside a proof/ directory) and the proof/ directories
(agda/proof/, agda/Untyped/proof/), which need not be read to trust the
results.  A module that mixes definitions and lemmas is split in two:
the definitions at agda/X.agda, the lemmas at agda/proof/X.agda (in the
untyped pipeline, agda/Untyped/X.agda and agda/Untyped/proof/X.agda).
For the counts below the two halves are one unit (as they were one
module before the split): they belong to the same group, and a proof
reaches the unit when it reaches either half.

Language-independent infrastructure (side 'infra') is reported in a
separate table and is not in any total.  The test is whether the code
would be used, unchanged, by other languages and compilers: abstract
binding trees and lemmas about the syntax of any signature, list lookups,
base types, typed indices and vectors, the denotational framework (sets
as predicates, environments, the semantics of any signature, DOp
signatures), the graph model (values, consistency, operators and their
continuity: the semantic algebra), the semantics of intrinsically typed
syntax in it, the small-step framework (transition systems, forward
simulations, runs from any state), the reduction framework and the
clocked one, all over any type of observations.  The meaning of this
compiler's primitives (Semantics/Graph/Prim.agda, as the machines' and
interpreters' prim?) and its observations (Semantics/Observation.agda)
are not infrastructure.  The operational values are not either.  For each
infrastructure group, the separate table shows the lines of its modules
that each proof reaches.  The script fails if an infrastructure module
imports a module that is not infrastructure.

The graph model's infrastructure is three groups, so that each semantic
algebra is charged only for the operators it uses: what any graph-model
semantics uses (values, consistency, the machinery for any operators,
and the operators both models share unchanged), the graph model's
operators, and the error monad of the graph model with errors.  The
graph model with errors is the fifth column; it is counted as the four
are, plus the graph model's meaning of the primitives, which it extends,
but the shared modules not counted are still those all four use.  The
script checks that it reaches no module of the other proofs but that
one.

A group may belong to two proofs ('op+red': the machines of Impᵀ, CFGᵀ
and X86ᵀ and the proofs of explicate control and select instructions,
shared by the CEK and reduction proofs); it is counted in full in that
row of both.

Import bundles (BUNDLES: Framework/GraphModel/Prelude.agda and
ErrorPrelude.agda, and their proof/ halves) only re-export other
modules, so that the semantics and proofs in the graph models open
them with one import.  They are not modules of their own here: they
belong to no group, and a module that imports one imports what it
re-exports (transitively), so a bundle changes no count.  The script
fails if a bundle has a line other than its module header and imports.

Totals come from the import graph (`import`/`open import` lines, with or
without `as`, `using`, module arguments or `public`).  A proof's total is
its own modules plus the shared modules it reaches transitively that are
not reached by all four proofs of its pipeline; shared modules reached
by all four are not counted anywhere, and infrastructure is never
counted.  Adequacy, an add-on to the denotational proof, also counts the
shared modules it reaches that the denotational total does not already
count.  The adequacy of the graph model with errors for Clos5ᵀ is
derived from the CEK column's simulation (PipelineSim); the CEK modules
it reaches that way are shown in their own row, not in its total.  The
script fails if one proof reaches another proof's modules (of either
pipeline), adequacy's, an example's or an experiment's, or if a module
outside agda/Untyped/ imports one inside it.

The ISWIMμ pilot (agda/Mu/, module prefix Mu.; sides 'mu-*', in no total
of the pipelines, nor in their tables): a typed ISWIM with iso-recursive
types and its compiler to X86μ, a parallel copy of the typed pipeline's
languages, passes and proofs, in the four styles.  --mu prints its own
main table, in the shape of the pipelines' (the four styles against each
other, the lowest of each row in bold; each column's total counts the
shared modules it reaches that the four do not all reach, and the typed
pipeline's modules it reuses, such as the meaning of the primitives and
the frameworks' instances at this compiler's observations), then its
adequacy (reported separately, against the typed pipeline's), the
no-error lemmas (in no total), the infrastructure by use, and its totals
per style against the typed pipeline's.  --mu-detail prints the pilot
against the typed pipeline row by row, per style.  Its groups are checked
as the others are (every module in one group), its columns must not
reach each other's modules (the CEK and reduction columns share the
machines of the first-order languages and the proofs of explicate control
and select instructions, 'mu-op+mu-red'), adequacy's, the no-error
lemmas' or the examples', nor a module of a proof of either pipeline
(what both pipelines share, such as the meaning of the primitives and the
small-step framework, they may use), and its infrastructure must import
only infrastructure; it has no theorem statements, so it is not on the
audit surface.

The public theorem statements are new boilerplate (each restates a
theorem of the proofs with its type), so they are not in the totals;
they are in the audit-surface table, which gives, for each style, the
lines of the audit surface that its statements reach: the shared part
(languages, passes, syntax), counted once, the semantics of that style,
and the statements.  The script fails if a module of the audit surface
imports a proof module (the theorem files do, by design), or if a module
outside the proof/ directories is not reached from the theorem files.
"""
import glob, os, re, sys

A = 'agda/'
U = 'agda/Untyped/'

L, C, PC = A + 'Language/', A + 'Compiler/', A + 'proof/Compiler/'
G, GP, GC = A + 'Semantics/Graph/', A + 'proof/Semantics/Graph/', A + 'proof/Correctness/Graph/'
O, OP, OC = A + 'Semantics/CEK/', A + 'proof/Semantics/CEK/', A + 'proof/Correctness/CEK/'
F, FP, FC = A + 'Semantics/Interp/', A + 'proof/Semantics/Interp/', A + 'proof/Correctness/Interp/'
RD, RP, RC = A + 'Semantics/Reduction/', A + 'proof/Semantics/Reduction/', A + 'proof/Correctness/Reduction/'
GE, GEP, GEC = A + 'Semantics/GraphErr/', A + 'proof/Semantics/GraphErr/', A + 'proof/Correctness/GraphErr/'
AP, GEA = A + 'proof/Adequacy/', A + 'proof/Adequacy/GraphErr/'
W, WP = A + 'Framework/', A + 'proof/Framework/'
MU = A + 'Mu/'
MUP = MU + 'proof/'


def u(p):
    """The path p of agda/, in the preserved untyped pipeline."""
    return U + p[len(A):]


# the sides of the four proofs that the five compare, all of them, and their
# adequacy proofs: the typed pipeline (the main one) and the untyped one
TYPED = dict(sides=('den', 'op', 'ck', 'red'), gerr='gerr', adeq='adeq', gadeq='gadeq',
             shared=('shared',), thm={'den': A + 'Theorems/Denotational.agda',
                                      'op': A + 'Theorems/Simulation.agda',
                                      'ck': A + 'Theorems/Interpreter.agda',
                                      'red': A + 'Theorems/Reduction.agda',
                                      'adeq': A + 'Theorems/Adequacy.agda',
                                      'gerr': A + 'Theorems/GraphErrors.agda'},
             exp='exp', name='typed pipeline')
UNTYPED = dict(sides=('uden', 'uop', 'uck', 'ured'), gerr='ugerr', adeq='uadeq', gadeq='ugadeq',
               shared=('shared', 'ushared'),
               thm={'uden': U + 'Theorems/Denotational.agda', 'uop': U + 'Theorems/Simulation.agda',
                    'uck': U + 'Theorems/Interpreter.agda', 'ured': U + 'Theorems/Reduction.agda',
                    'uadeq': U + 'Theorems/Adequacy.agda', 'ugerr': U + 'Theorems/GraphErrors.agda'},
               exp='uexp', name='untyped pipeline (preserved)')
BOTH = 'den+uden'

# the statements of the assurance (side 'assure'), not in the totals
ASSURE_THM = A + 'Theorems/X86Erasure.agda'

# import bundles: imports only, looked through (see above)
BUNDLES = {W + 'GraphModel/Prelude.agda', W + 'GraphModel/ErrorPrelude.agda',
           WP + 'GraphModel/Prelude.agda', WP + 'GraphModel/ErrorPrelude.agda'}

# (side, group, glob patterns)
GROUPS = [
    # the languages, the passes and the lemmas about their output that the
    # proofs use (cast insertion on closed programs, globalize's references,
    # select's labels and frames, simplify keeps programs closed), and the
    # observations.  Those not used by all four proofs of a pipeline are
    # counted in each proof that uses them (see main).  Untyped ISWIM, the
    # primitives, simplify and the observations are used by both
    # pipelines; untyped X86 is the untyped pipeline's target.
    ('shared', 'syntax, languages, compiler passes',
     [L + '*.agda', L + 'Typed/*.agda', C + '*.agda', PC + '*.agda', A + 'Semantics/Observation.agda']),
    ('ushared', 'syntax, languages, compiler passes',
     [u(L) + '*.agda', u(C) + '*.agda', u(PC) + '*.agda', L + 'X86.agda']),

    # assurance, not in the totals: with the types erased, select emits the
    # instructions of select into untyped X86 (the typed pipeline's select
    # before X86ᵀ, Compiler/SelectX86.agda)
    ('assure', 'erasure: select emits the instructions of select into untyped X86',
     [L + 'Typed/X86Erase.agda', C + 'SelectX86.agda', PC + 'SelectErase.agda']),
    # and erasing X86ᵀ keeps the meaning of every program, in the CEK
    # machines (a simulation of the X86ᵀ machine by the X86 machine)
    ('assure', 'erasure keeps the meaning of every X86ᵀ program (CEK machines)',
     [A + 'proof/Assurance/*.agda']),

    # language-independent infrastructure: not in the totals (see main)
    ('infra', 'abstract binding trees',
     [W + 'abt/AbstractBindingTree.agda', W + 'abt/GSubst.agda', W + 'abt/ScopedTuple.agda',
      WP + 'abt/ScopedTuple.agda', W + 'abt/Sig.agda', W + 'abt/Var.agda',
      W + 'Syntax/SigUtil.agda', W + 'Syntax/SyntaxUtil.agda']),
    ('infra', 'syntax lemmas (renaming, scoping, uses, substitution), list lookups',
     [W + 'Syntax/Uses.agda', W + 'Syntax/Scope.agda', W + 'Syntax/Rename.agda', W + 'Syntax/Subst.agda',
      W + 'Syntax/ScopeDec.agda', W + 'Syntax/Kit.agda', WP + 'Syntax/*.agda',
      W + 'ListUtil.agda', WP + 'ListUtil.agda']),
    ('infra', 'base types, logical equivalence', [W + 'Primitives.agda', W + 'PrimitivesDec.agda', W + 'Iff.agda']),
    ('infra', 'typed indices, lookup in typed lists, vectors (collecting, selecting, projecting)',
     [W + 'Membership.agda', W + 'Lookup.agda', WP + 'Lookup.agda', W + 'VecUtil.agda', WP + 'VecUtil.agda',
      W + 'VecSelect.agda', WP + 'VecSelect.agda', WP + 'VecProj.agda']),
    ('infra', 'denotational framework',
     [W + 'GraphModel/SetsAsPredicates.agda', WP + 'GraphModel/SetsAsPredicates.agda',
      W + 'GraphModel/DOpSig.agda', WP + 'GraphModel/DOpSig.agda',
      W + 'GraphModel/Env.agda', WP + 'GraphModel/Env.agda',
      WP + 'GraphModel/Semantics.agda', WP + 'GraphModel/DenotProperties.agda',
      W + 'abt/Fold2.agda', WP + 'GraphModel/RenameSem.agda',
      WP + 'GraphModel/SemanticsUses.agda']),
    # the graph model is three groups, so that each semantic algebra is
    # charged only for the operators it uses: the values, their consistency
    # and the machinery for any operators (continuity, Good, the properties
    # of whole terms), with the operators both algebras share unchanged
    # (constants, components of a tuple of results); the operators of the
    # graph model; and the error monad of the graph model with errors
    ('infra', 'graph model: values, consistency, machinery for any operators',
     [W + 'GraphModel/Domain.agda', WP + 'GraphModel/Domain.agda',
      W + 'GraphModel/OpsBase.agda', WP + 'GraphModel/OpsBase.agda',
      WP + 'GraphModel/ContinuityBase.agda', WP + 'GraphModel/SemanticsCore.agda',
      WP + 'GraphModel/DomainUtilBase.agda']),
    ('infra', 'graph model: its operators',
     [W + 'GraphModel/Ops.agda', WP + 'GraphModel/Ops.agda',
      WP + 'GraphModel/Continuity.agda', WP + 'GraphModel/SemanticsUtil.agda',
      WP + 'GraphModel/DomainUtil.agda', WP + 'GraphModel/Strict.agda', WP + 'GraphModel/Laws.agda']),
    ('infra', 'graph model with errors: the error monad, its operators and laws',
     [W + 'GraphModel/ErrorMonad.agda', WP + 'GraphModel/ErrorMonad.agda']),
    ('infra', 'graph model: semantics of intrinsically typed syntax',
     [W + 'GraphModel/Typed*.agda', WP + 'GraphModel/Typed*.agda']),
    ('infra', 'small-step framework: transition systems, simulations',
     [W + 'Smallstep.agda', WP + 'Smallstep.agda', WP + 'Simulation.agda', WP + 'Both.agda']),
    ('infra', 'reduction framework: reduction semantics, simulations between them',
     [W + 'Reduction.agda', WP + 'Reduction.agda', W + 'ReductionVec.agda', WP + 'ReductionVec.agda']),
    ('infra', 'clocked big-step framework', [W + 'Clocked.agda', WP + 'Clocked.agda']),
    # runs of a step function from any state, for the logical relations of
    # adequacy
    ('infra', 'runs of a step function from any state', [WP + 'Runs.agda']),

    # simplify's syntactic lemmas (SimplifyFacts) are used by all ten of its
    # proofs (five columns, two pipelines), so they are counted in the
    # simplify row of each column
    ('den+op+ck+red+gerr+uden+uop+uck+ured+ugerr', 'simplify', [PC + 'SimplifyFacts.agda']),

    # --- the plain graph model ------------------------------------------------
    # the meaning of the primitives (Prim.agda) is here, as prim? is in each
    # machine and interpreter
    (BOTH, 'semantics of the languages',
     [G + 'Prim.agda', GP + 'Prim.agda', G + 'ISWIM.agda', GP + 'ISWIM.agda', GP + 'ISWIMContinuous.agda']),
    ('den', 'semantics of the languages', [G + 'Typed/*.agda', GP + 'Typed/*.agda']),
    (BOTH, 'simplify', [GC + 'SimplifyCorrect.agda']),
    ('den', 'cast insertion', [GC + 'CastCorrect.agda']),
    ('den', 'CC: enclose', [GC + 'EncloseCorrect.agda']),
    ('den', 'CC: optimize', [GC + 'OptimizeCorrect.agda']),
    ('den', 'CC: concretize', [GC + 'ConcretizeCorrect.agda']),
    ('den', 'CC: delay', [GC + 'Delay*.agda']),
    ('den', 'CC: globalize', [GC + 'GlobalizeCorrect.agda']),
    ('den', 'rco', [GC + 'RCOCorrect.agda']),
    ('den', 'lift locals', [GC + 'LiftLocalsCorrect.agda']),
    ('den', 'explicate control', [GC + 'ExplicateCorrect.agda']),
    ('den', 'select instructions', [GC + 'SelectCorrect.agda']),
    ('den', 'composition', [GC + 'CompilerCorrect.agda']),

    # --- CEK machines + simulations ------------------------------------------
    # with the framework at this compiler's observations (Smallstep.agda,
    # Simulation.agda).  The machines of Clos5ᵀ (whose values Impᵀ's uses),
    # Impᵀ, CFGᵀ and X86ᵀ, and the framework instances, are shared with the
    # reduction proof ('op+red': counted in both columns).  The machine of
    # untyped X86 and its values are the untyped pipeline's.
    ('op+uop', 'semantics of the languages', [O + 'ISWIM.agda']),
    ('op+red+uop+ured', 'semantics of the languages',
     [O + 'Smallstep.agda', OP + 'Smallstep.agda', OP + 'Simulation.agda']),
    ('uop+ured', 'semantics of the languages', [O + 'Values.agda', O + 'X86.agda']),
    ('op', 'semantics of the languages',
     [O + 'Typed/ISWIM.agda', O + 'Typed/Clos2.agda', O + 'Typed/Clos3.agda', O + 'Typed/Clos4.agda']),
    ('op+red', 'semantics of the languages',
     [O + 'Typed/Clos5.agda', O + 'Typed/Imp.agda', O + 'Typed/CFG.agda', O + 'Typed/X86.agda']),
    # what several pass proofs share: Lock, the steps of project (Common), and
    # the Clos5ᵀ machine on atoms (Clos5Common, rco and lift locals)
    ('op', 'lemmas shared by the passes', [OC + 'Common.agda', OC + 'Clos5Common.agda']),
    ('op+uop', 'simplify', [OC + 'SimplifySim.agda']),
    # with 48 lines of list and primitive lemmas copied from adequacy, so
    # that the CEK proof does not import it (CastSimLemmas)
    ('op', 'cast insertion', [OC + 'CastSim.agda', OC + 'CastSimLemmas.agda']),
    ('op', 'CC: enclose', [OC + 'EncloseSim.agda']),
    ('op', 'CC: optimize', [OC + 'OptimizeSim.agda']),
    ('op', 'CC: concretize', [OC + 'ConcretizeSim.agda']),
    ('op', 'CC: delay', [OC + 'DelaySim.agda']),
    ('op', 'CC: globalize', [OC + 'GlobalizeSim.agda']),
    ('op', 'rco', [OC + 'RCOSim.agda']),
    ('op', 'lift locals', [OC + 'LiftLocalsSim.agda']),
    # explicate control and select instructions are between the machines of
    # first-order languages, and are shared with the reduction proof
    ('op+red', 'explicate control', [OC + 'ExplicateSim.agda']),
    ('op+red', 'select instructions', [OC + 'SelectSim.agda']),
    ('op', 'composition', [OC + 'PipelineSim.agda']),

    # --- clocked interpreters + value relations --------------------------------
    # with the framework at this compiler's observations (Clock.agda)
    ('ck+uck', 'semantics of the languages', [F + 'ISWIM.agda', F + 'Clock.agda', FP + 'Clock.agda']),
    ('ck', 'semantics of the languages', [F + 'Typed/*.agda', FP + 'Typed/*.agda']),
    ('ck+uck', 'simplify', [FC + 'SimplifyFuel.agda']),
    ('ck', 'cast insertion', [FC + 'CastFuel.agda']),
    ('ck', 'CC: enclose', [FC + 'EncloseFuel.agda']),
    ('ck', 'CC: optimize', [FC + 'OptimizeFuel.agda']),
    ('ck', 'CC: concretize', [FC + 'ConcretizeFuel.agda']),
    ('ck', 'CC: delay', [FC + 'DelayFuel.agda']),
    ('ck', 'CC: globalize', [FC + 'GlobalizeFuel.agda']),
    ('ck', 'rco', [FC + 'RCOFuel.agda']),
    ('ck', 'lift locals', [FC + 'LiftLocalsFuel.agda']),
    ('ck', 'explicate control', [FC + 'ExplicateFuel.agda']),
    ('ck', 'select instructions', [FC + 'SelectFuel.agda']),
    ('ck', 'composition', [FC + 'CompilerFuel.agda']),

    # --- reduction semantics + simulations -------------------------------------
    # reduction semantics (substitution) for the languages with binders, and
    # the framework at this compiler's observations (Smallstep.agda)
    ('red+ured', 'semantics of the languages', [RD + 'ISWIM.agda', RD + 'Smallstep.agda']),
    ('red', 'semantics of the languages', [RD + 'Typed/*.agda', RP + 'Typed/*.agda']),
    ('red+ured', 'simplify', [RC + 'SimplifyRed.agda']),
    ('red', 'cast insertion', [RC + 'CastRed.agda']),
    ('red', 'CC: enclose', [RC + 'EncloseRed.agda']),
    ('red', 'CC: optimize', [RC + 'OptimizeRed.agda']),
    ('red', 'CC: concretize', [RC + 'ConcretizeRed.agda']),
    ('red', 'CC: delay', [RC + 'DelayRed.agda']),
    ('red', 'CC: globalize', [RC + 'GlobalizeRed.agda']),
    ('red', 'rco', [RC + 'RCORed.agda']),
    ('red', 'lift locals', [RC + 'LiftLocalsRed.agda']),
    ('red', 'composition', [RC + 'PipelineRed.agda']),

    # --- the graph model with errors -------------------------------------------
    ('gerr+ugerr', 'semantics of the languages',
     [GE + 'Prim.agda', GEP + 'Prim.agda', GE + 'ISWIM.agda', GEP + 'ISWIM.agda']),
    ('gerr', 'semantics of the languages', [GE + 'Typed/*.agda', GEP + 'Typed/*.agda']),
    ('gerr+ugerr', 'simplify', [GEC + 'SimplifyCorrect.agda']),
    ('gerr', 'cast insertion', [GEC + 'CastCorrect.agda']),
    ('gerr', 'CC: enclose', [GEC + 'EncloseCorrect.agda']),
    ('gerr', 'CC: optimize', [GEC + 'OptimizeCorrect.agda']),
    ('gerr', 'CC: concretize', [GEC + 'ConcretizeCorrect.agda']),
    ('gerr', 'CC: delay', [GEC + 'Delay*.agda']),
    ('gerr', 'CC: globalize', [GEC + 'GlobalizeCorrect.agda']),
    ('gerr', 'rco', [GEC + 'RCOCorrect.agda']),
    ('gerr', 'lift locals', [GEC + 'LiftLocalsCorrect.agda']),
    ('gerr', 'explicate control', [GEC + 'ExplicateCorrect.agda']),
    ('gerr', 'select instructions', [GEC + 'SelectCorrect.agda']),
    ('gerr', 'composition', [GEC + 'CompilerCorrect.agda']),

    # --- adequacy ----------------------------------------------------------------
    # of the graph model: ISWIM is that of both pipelines; X86ᵀ is direct
    ('adeq+uadeq', 'ISWIM', [AP + 'Common.agda', AP + 'Soundness.agda', AP + 'LogRel.agda', AP + 'ISWIM.agda']),
    ('adeq', 'Clos5', [AP + 'Clos5*.agda']),
    ('adeq', 'X86ᵀ', [AP + 'X86*.agda']),
    # that the table of compile-x86 M is consistent and holds each
    # definition's code (as Clos5ᵀ's, from globalize-older)
    ('adeq', 'well-formedness of compiled programs', [AP + 'X86Compiled.agda']),
    ('adeq', 'end to end', [AP + 'EndToEnd.agda']),
    # of the graph model with errors: X86ᵀ is direct; its Clos5ᵀ adequacy is
    # derived from the simulation of the CEK column, in its end to end
    # (GraphErr/EndToEnd)
    ('gadeq+ugadeq', 'ISWIM', [GEA + 'Soundness.agda', GEA + 'LogRel.agda', GEA + 'ISWIM.agda']),
    ('gadeq', 'X86ᵀ', [GEA + 'X86*.agda']),
    ('gadeq+ugadeq', 'end to end', [GEA + 'Agree.agda']),
    ('gadeq', 'end to end', [GEA + 'EndToEnd.agda']),
    ('gadeq+ugadeq', 'simplify through the ISWIM machine', [GEA + 'Simplify.agda']),

    ('examples', 'examples', [PC + 'Examples/*.agda']),

    # not in the totals: the public theorem statements (see the audit-surface
    # table)
    ('thm', 'theorem statements', [A + 'Theorems/*.agda']),

    # --- the untyped pipeline, preserved ---------------------------------------
    ('uden', 'semantics of the languages',
     [u(G) + 'Frames.agda', u(G) + 'X86.agda', u(GP) + 'X86.agda', u(G) + 'Clos2Iswim.agda', u(GP) + 'Clos2Iswim.agda', u(G) + 'Clos3Iswim.agda', u(GP) + 'Clos3Iswim.agda',
      u(G) + 'Clos4Iswim.agda', u(GP) + 'Clos4Iswim.agda', u(G) + 'Clos5Iswim.agda',
      u(GP) + 'Clos5IswimContinuous.agda', u(G) + 'Imp.agda', u(G) + 'ImpK.agda', u(G) + 'CFG.agda']),
    ('uden', 'CC: enclose', [u(GC) + 'EncloseCorrect.agda']),
    ('uden', 'CC: optimize', [u(GC) + 'OptimizeCorrect.agda']),
    ('uden', 'CC: concretize', [u(GC) + 'ConcretizeCorrect.agda']),
    ('uden', 'CC: delay',
     [u(GC) + 'DelayFiniteCommon.agda', u(GC) + 'DelayFiniteRel.agda', u(GC) + 'DelayApp.agda',
      u(GC) + 'DelayPreserve.agda', u(GC) + 'DelayReflectFinite.agda']),
    ('uden', 'CC: globalize', [u(GC) + 'GlobalizeCorrect.agda']),
    ('uden', 'rco', [u(GC) + 'RCOCorrect.agda']),
    # against the continuation-passing semantics of Imp; against the direct
    # one, see 'uexp'
    ('uden', 'lift locals', [u(GC) + 'LiftLocalsCommon.agda', u(GC) + 'LiftLocalsCorrectK.agda']),
    ('uden', 'explicate control', [u(GC) + 'ExplicateCommon.agda', u(GC) + 'ExplicateCorrectK.agda']),
    ('uden', 'select instructions', [u(GC) + 'SelectCorrect.agda']),
    ('uden', 'composition', [u(GC) + 'CompilerCorrect.agda']),
    ('uop', 'semantics of the languages',
     [u(O) + 'Clos2.agda', u(O) + 'Clos3.agda', u(O) + 'Clos4.agda', u(O) + 'Clos5.agda']),
    ('uop+ured', 'semantics of the languages', [u(O) + 'Imp.agda', u(O) + 'CFG.agda']),
    ('uop', 'CC: enclose', [u(OC) + 'EncloseSim.agda']),
    ('uop', 'CC: optimize', [u(OC) + 'OptimizeSim.agda']),
    ('uop', 'CC: concretize', [u(OC) + 'ConcretizeSim.agda']),
    ('uop', 'CC: delay', [u(OC) + 'DelaySim.agda']),
    ('uop', 'CC: globalize', [u(OC) + 'GlobalizeSim.agda']),
    ('uop', 'rco', [u(OC) + 'RCOSim.agda']),
    ('uop', 'lift locals', [u(OC) + 'LiftLocalsSim.agda']),
    ('uop+ured', 'explicate control', [u(OC) + 'ExplicateSim.agda']),
    ('uop+ured', 'select instructions', [u(OC) + 'SelectSim.agda']),
    ('uop', 'composition', [u(OC) + 'CompilerSim.agda', u(OC) + 'CompilerX86Sim.agda']),
    ('ured', 'semantics of the languages', [u(RD) + '*.agda', u(RP) + '*.agda']),
    ('ured', 'CC: enclose', [u(RC) + 'EncloseRed.agda']),
    ('ured', 'CC: optimize', [u(RC) + 'OptimizeRed.agda']),
    ('ured', 'CC: concretize', [u(RC) + 'ConcretizeRed.agda']),
    ('ured', 'CC: delay', [u(RC) + 'DelayRed.agda']),
    ('ured', 'CC: globalize', [u(RC) + 'GlobalizeRed.agda']),
    ('ured', 'rco', [u(RC) + 'RCORed.agda']),
    ('ured', 'lift locals', [u(RC) + 'LiftLocalsRed.agda']),
    ('ured', 'composition', [u(RC) + 'CompilerRed.agda', u(RC) + 'CompilerX86Red.agda']),
    ('uck', 'semantics of the languages', [u(F) + '*.agda']),
    ('uck', 'CC: enclose', [u(FC) + 'EncloseFuel.agda']),
    ('uck', 'CC: optimize', [u(FC) + 'OptimizeFuel.agda']),
    ('uck', 'CC: concretize', [u(FC) + 'ConcretizeFuel.agda']),
    ('uck', 'CC: delay', [u(FC) + 'DelayFuel.agda']),
    ('uck', 'CC: globalize', [u(FC) + 'GlobalizeFuel.agda']),
    ('uck', 'rco', [u(FC) + 'RCOFuel.agda']),
    ('uck', 'lift locals', [u(FC) + 'LiftLocalsFuel.agda']),
    ('uck', 'explicate control', [u(FC) + 'ExplicateFuel.agda']),
    ('uck', 'select instructions', [u(FC) + 'SelectFuel.agda']),
    ('uck', 'composition', [u(FC) + 'CompilerFuel.agda']),
    ('ugerr', 'semantics of the languages', [u(GE) + '*.agda', u(GEP) + '*.agda']),
    ('ugerr', 'CC: enclose', [u(GEC) + 'EncloseCorrect.agda']),
    ('ugerr', 'CC: optimize', [u(GEC) + 'OptimizeCorrect.agda']),
    ('ugerr', 'CC: concretize', [u(GEC) + 'ConcretizeCorrect.agda']),
    ('ugerr', 'CC: delay', [u(GEC) + 'Delay*.agda']),
    ('ugerr', 'CC: globalize', [u(GEC) + 'GlobalizeCorrect.agda']),
    ('ugerr', 'rco', [u(GEC) + 'RCOCorrect.agda']),
    ('ugerr', 'lift locals', [u(GEC) + 'LiftLocalsCorrect.agda']),
    ('ugerr', 'explicate control', [u(GEC) + 'ExplicateCorrect.agda']),
    ('ugerr', 'select instructions', [u(GEC) + 'SelectCorrect.agda']),
    ('ugerr', 'composition', [u(GEC) + 'CompilerCorrect.agda']),
    ('uadeq', 'Clos5', [u(AP) + 'Clos5Common.agda', u(AP) + 'Clos5Soundness.agda', u(AP) + 'Clos5LogRel.agda',
                        u(AP) + 'Clos5.agda']),
    ('uadeq', 'X86',
     [u(AP) + 'X86Common.agda', u(AP) + 'X86Soundness.agda', u(AP) + 'X86LogRel.agda', u(AP) + 'X86.agda',
      u(AP) + 'Values.agda']),
    ('uadeq', 'well-formedness of compiled programs',
     [u(AP) + 'Clos5WF.agda', u(AP) + 'CompileWF.agda', u(AP) + 'X86CompileWF.agda', u(AP) + 'X86WF.agda']),
    ('uadeq', 'end to end', [u(AP) + 'EndToEnd.agda', u(AP) + 'ISWIMCompile.agda']),
    ('ugadeq', 'Clos5', [u(GEA) + 'Clos5Common.agda', u(GEA) + 'Clos5Soundness.agda', u(GEA) + 'Clos5LogRel.agda',
                         u(GEA) + 'Clos5.agda']),
    ('ugadeq', 'X86',
     [u(GEA) + 'X86Common.agda', u(GEA) + 'X86Consistent.agda', u(GEA) + 'X86Soundness.agda',
      u(GEA) + 'X86LogRel.agda', u(GEA) + 'X86.agda']),
    ('ugadeq', 'well-formedness of compiled programs',
     [u(GEA) + 'Clos5WF.agda', u(GEA) + 'X86CompileWF.agda', u(GEA) + 'X86WF.agda']),
    ('ugadeq', 'end to end', [u(GEA) + 'EndToEnd.agda']),
    ('uexamples', 'examples', [u(GC) + '*Example.agda', u(PC) + 'Examples/*.agda']),
    # not in the totals: a direct backward simulation for delay, without
    # determinism, and the direct semantics of Imp (ImpDirect.agda) with lift
    # locals and explicate control proved against it (see loc.md)
    ('uexp', 'simulation: direct backward simulation for delay — framework', [u(OP) + 'Backward.agda']),
    ('uexp', 'simulation: direct backward simulation for delay — delay', [u(OC) + 'DelayBackSim.agda']),
    ('uexp', 'graph model: direct Imp — semantics', [u(GP) + 'ImpDirect.agda']),
    ('uexp', 'graph model: direct Imp — lift locals', [u(GC) + 'LiftLocalsCorrect.agda']),
    ('uexp', 'graph model: direct Imp — explicate control', [u(GC) + 'ExplicateCorrect.agda']),
    ('uthm', 'theorem statements', [U + 'Theorems/*.agda']),

    # --- the ISWIMμ pilot (agda/Mu/), in no total ------------------------------
    ('mu-shared', 'syntax, languages, compiler passes', [MU + 'Language/*.agda', MU + 'Compiler/*.agda']),
    ('mu-infra', 'heterogeneous vectors: lookup, collecting, selecting, relating', [MU + 'Framework/*.agda']),
    ('mu-den', 'semantics of the languages', [MU + 'Semantics/Graph/*.agda', MUP + 'Semantics/Graph/*.agda']),
    ('mu-den', 'CC: enclose', [MUP + 'Correctness/Graph/EncloseCorrect.agda']),
    ('mu-den', 'CC: optimize', [MUP + 'Correctness/Graph/OptimizeCorrect.agda']),
    ('mu-den', 'CC: concretize', [MUP + 'Correctness/Graph/ConcretizeCorrect.agda']),
    ('mu-den', 'CC: delay', [MUP + 'Correctness/Graph/Delay*.agda']),
    ('mu-den', 'CC: globalize', [MUP + 'Correctness/Graph/GlobalizeCorrect.agda']),
    ('mu-den', 'rco', [MUP + 'Correctness/Graph/RCOCorrect.agda']),
    ('mu-den', 'lift locals', [MUP + 'Correctness/Graph/LiftLocalsCorrect.agda']),
    ('mu-den', 'explicate control', [MUP + 'Correctness/Graph/ExplicateCorrect.agda']),
    ('mu-den', 'select instructions', [MUP + 'Correctness/Graph/SelectCorrect.agda']),
    ('mu-den', 'composition', [MUP + 'Correctness/Graph/CompilerCorrect.agda']),
    # the machines of ISWIMμ and Clos2μ–Clos4μ; those of Clos5μ, Impμ, CFGμ
    # and X86μ, with the proofs of explicate control and select
    # instructions, are shared with the reduction column ('mu-op+mu-red'),
    # as the typed pipeline's are ('op+red')
    ('mu-op', 'semantics of the languages', [MU + 'Semantics/CEK/' + x + '.agda' for x in ('ISWIM', 'Clos2', 'Clos3', 'Clos4')]),
    ('mu-op+mu-red', 'semantics of the languages', [MU + 'Semantics/CEK/' + x + '.agda' for x in ('Clos5', 'Imp', 'CFG', 'X86')]),
    ('mu-op', 'CC: enclose', [MUP + 'Correctness/CEK/EncloseSim.agda']),
    ('mu-op', 'CC: optimize', [MUP + 'Correctness/CEK/OptimizeSim.agda']),
    ('mu-op', 'CC: concretize', [MUP + 'Correctness/CEK/ConcretizeSim.agda']),
    ('mu-op', 'CC: delay', [MUP + 'Correctness/CEK/DelaySim.agda']),
    ('mu-op', 'lemmas shared by the passes', [MUP + 'Correctness/CEK/Clos5Common.agda']),
    ('mu-op', 'CC: globalize', [MUP + 'Correctness/CEK/GlobalizeSim.agda']),
    ('mu-op', 'rco', [MUP + 'Correctness/CEK/RCOSim.agda']),
    ('mu-op', 'lift locals', [MUP + 'Correctness/CEK/LiftLocalsSim.agda']),
    ('mu-op+mu-red', 'explicate control', [MUP + 'Correctness/CEK/ExplicateSim.agda']),
    ('mu-op+mu-red', 'select instructions', [MUP + 'Correctness/CEK/SelectSim.agda']),
    ('mu-op', 'composition', [MUP + 'Correctness/CEK/PipelineSim.agda']),
    ('mu-ck', 'semantics of the languages', [MU + 'Semantics/Interp/*.agda', MUP + 'Semantics/Interp/*.agda']),
    ('mu-ck', 'CC: enclose', [MUP + 'Correctness/Interp/EncloseFuel.agda']),
    ('mu-ck', 'CC: optimize', [MUP + 'Correctness/Interp/OptimizeFuel.agda']),
    ('mu-ck', 'CC: concretize', [MUP + 'Correctness/Interp/ConcretizeFuel.agda']),
    ('mu-ck', 'CC: delay', [MUP + 'Correctness/Interp/DelayFuel.agda']),
    ('mu-ck', 'CC: globalize', [MUP + 'Correctness/Interp/GlobalizeFuel.agda']),
    ('mu-ck', 'rco', [MUP + 'Correctness/Interp/RCOFuel.agda']),
    ('mu-ck', 'lift locals', [MUP + 'Correctness/Interp/LiftLocalsFuel.agda']),
    ('mu-ck', 'explicate control', [MUP + 'Correctness/Interp/ExplicateFuel.agda']),
    ('mu-ck', 'select instructions', [MUP + 'Correctness/Interp/SelectFuel.agda']),
    ('mu-ck', 'composition', [MUP + 'Correctness/Interp/CompilerFuel.agda']),
    # P2: that no semantics of ISWIMμ or X86μ stops with an error (the
    # graph model's end-to-end theorem through adequacy needs the CEK
    # machines'; the others are stated for completeness), in no column
    ('mu-noerr', 'CEK machines of ISWIMμ and X86μ (X86μ\'s is also the reduction column\'s)',
     [MUP + 'Semantics/CEK/NoError.agda']),
    ('mu-noerr', 'clocked interpreters of ISWIMμ and X86μ', [MUP + 'Semantics/Interp/NoError.agda']),
    ('mu-noerr', 'reduction semantics of ISWIMμ', [MUP + 'Semantics/Reduction/NoError.agda']),
    # P2: adequacy of the graph model, for the ISWIMμ machine and the X86μ
    # machine (direct), as the typed pipeline's ('adeq'); no Clos5μ
    # adequacy, which the end-to-end theorem into X86μ does not need
    ('mu-adeq', 'ISWIM', [MUP + 'Adequacy/' + x + '.agda' for x in ('ISWIMOk', 'Tuples', 'Soundness', 'LogRel', 'ISWIM')]),

    ('mu-examples', 'examples', [MUP + 'Compiler/Examples/*.agda']),
    # the pilot's reduction column (in --mu's reduction table): reduction
    # semantics of the languages with binders, the simulations, and the
    # reduction framework for heterogeneous vectors (infrastructure); it
    # shares the CEK column's machines of the first-order languages and its
    # proofs of explicate control and select instructions (MU_RED_SHARED), as
    # the typed pipeline's reduction column does ('op+red')
    ('mu-red', 'semantics of the languages', [MU + 'Semantics/Reduction/*.agda', MUP + 'Semantics/Reduction/*.agda']),
    ('mu-red', 'CC: enclose', [MUP + 'Correctness/Reduction/EncloseRed.agda']),
    ('mu-red', 'CC: optimize', [MUP + 'Correctness/Reduction/OptimizeRed.agda']),
    ('mu-red', 'CC: concretize', [MUP + 'Correctness/Reduction/ConcretizeRed.agda']),
    ('mu-red', 'CC: delay', [MUP + 'Correctness/Reduction/DelayRed.agda']),
    ('mu-red', 'CC: globalize', [MUP + 'Correctness/Reduction/GlobalizeRed.agda']),
    ('mu-red', 'rco', [MUP + 'Correctness/Reduction/RCORed.agda']),
    ('mu-red', 'lift locals', [MUP + 'Correctness/Reduction/LiftLocalsRed.agda']),
    ('mu-red', 'composition', [MUP + 'Correctness/Reduction/PipelineRed.agda']),
    ('mu-rinfra', 'reduction of heterogeneous vectors', [MU + 'Framework/ReductionAll.agda']),
]

ADEQ_ROWS = ['ISWIM', 'Clos5', 'X86', 'X86ᵀ', 'well-formedness of compiled programs', 'end to end',
             'simplify through the ISWIM machine']
ROWS = ['semantics of the languages', 'lemmas shared by the passes', 'simplify', 'cast insertion',
        'CC: enclose', 'CC: optimize', 'CC: concretize', 'CC: delay', 'CC: globalize', 'rco',
        'lift locals', 'explicate control', 'select instructions', 'composition']

# the style of each side, for the independence checks and the labels
STYLE = {}
for _p in (TYPED, UNTYPED):
    for _s, _t in zip(_p['sides'] + (_p['gerr'], _p['adeq'], _p['gadeq']),
                      ('den', 'op', 'ck', 'red', 'gerr', 'adeq', 'gadeq')):
        STYLE[_s] = _t
LABELS = {'den': 'denotational: graph model', 'op': 'CEK machine + simulation',
          'ck': 'clocked interpreter + value relations',
          'red': 'reduction semantics + simulation', 'adeq': 'adequacy',
          'gerr': 'graph model with errors', 'gadeq': 'adequacy with errors'}
NAMES = {'den': 'graph model', 'op': 'simulation', 'ck': 'interpreter',
         'red': 'reduction', 'adeq': 'adequacy', 'gerr': 'graph model with errors',
         'gadeq': 'adequacy with errors'}
EXTRA = 'shared modules not used by all four proofs'


def tag(P):
    """The marker of the untyped pipeline's tables, so that their header lines
    differ from the main ones."""
    return '' if P is TYPED else ' (untyped pipeline)'


def label(s):
    return LABELS[STYLE[s]]


def name(s):
    return NAMES[STYLE[s]]


def strip_comments(s):
    """The text of s without {- -} blocks and -- line comments (newlines kept)."""
    out, i, depth = [], 0, 0
    while i < len(s):
        if s.startswith('{-', i):
            depth += 1; i += 2; continue
        if depth and s.startswith('-}', i):
            depth -= 1; i += 2; continue
        if depth:
            if s[i] == '\n':
                out.append('\n')
            i += 1; continue
        out.append(s[i]); i += 1
    return '\n'.join(re.sub(r'(^|\s)--.*$', '', line)
                     for line in ''.join(out).split('\n'))


IMPORT_START = re.compile(r'(\s*)(?:open\s+)?import\b')

_CODE = {}


def code_lines(path):
    """The code lines of path, not counting import statements: a line that
    starts with `import` or `open import`, and the lines after it that are
    indented more deeply (its continuation)."""
    if path in _CODE:
        return _CODE[path]
    text = strip_comments(open(path, encoding='utf-8').read())
    n, indent = 0, None
    for line in text.split('\n'):
        if not line.strip():
            continue
        col = len(line) - len(line.lstrip())
        if indent is not None and col > indent:
            continue
        m = IMPORT_START.match(line)
        indent = len(m.group(1)) if m else None
        if not m:
            n += 1
    _CODE[path] = n
    return n


# `import M`, `open import M`, `import M as X`, `open import M args using (…)`,
# `… public`, with the module name possibly on the next line.
IMPORT = re.compile(r'(?<![^\s;{(])(?:open\s+)?import\s+([^\s;(){}]+)')


def imports(path):
    """Files under agda/ that path imports (library modules are ignored),
    with each import bundle replaced by the files it re-exports."""
    text = strip_comments(open(path, encoding='utf-8').read())
    out = set()
    for m in IMPORT.finditer(text):
        f = 'agda/' + m.group(1).replace('.', '/') + '.agda'
        if f in BUNDLES:
            out |= imports(f)
        elif os.path.exists(f):
            out.add(f)
    return out


def is_proof(f):
    return f.startswith(A + 'proof/') or f.startswith(U + 'proof/') or f.startswith(MUP)


def unit(f):
    """The unit of a file: agda/X.agda for both agda/X.agda and its proof half
    agda/proof/X.agda (likewise under agda/Untyped/ and agda/Mu/)."""
    if f.startswith(MUP):
        return MU + f[len(MUP):]
    if f.startswith(U + 'proof/'):
        return U + f[len(U + 'proof/'):]
    if f.startswith(A + 'proof/'):
        return A + f[len(A + 'proof/'):]
    return f


def reachable(roots, graph, avoid=frozenset()):
    """The units reachable from roots, not entering those in avoid."""
    seen, todo = set(), [r for r in roots if r not in avoid]
    while todo:
        f = todo.pop()
        if f not in seen:
            seen.add(f)
            todo.extend(g for g in graph[f] if g not in avoid)
    return seen


def modname(f):
    return f[len("agda/"):-len(".agda")].replace("/", ".")


def sides_of(side):
    """The proofs a group belongs to: 'op+red' is counted in both."""
    return side.split('+')


def bold_min(ns):
    """Cells for the numbers ns (None for a missing entry), with the lowest
    in bold when at least two entries are present: the best result."""
    present = [n for n in ns if n is not None]
    low = min(present) if len(present) >= 2 else None
    return [('—' if n is None else f'**{n}**' if n == low else str(n)) for n in ns]


class Count:
    """The groups, units, import graph and checks; then each pipeline's
    counts (analyze)."""

    def __init__(self):
        seen, counts, files_of = {}, {}, {}
        # a file named explicitly by a group is not matched by another's wildcard
        explicit = {p for _, _, pats in GROUPS for p in pats if '*' not in p}
        for b in sorted(BUNDLES):
            # a bundle has only its module header and imports
            if code_lines(b) != 1:
                sys.exit(f'{b}, an import bundle, has lines other than imports')
        for side, gname, pats in GROUPS:
            files = sorted({f for p in pats for f in glob.glob(p)
                            if ('*' not in p or f not in explicit) and f not in BUNDLES})
            if not files:
                sys.exit(f'no files for group {side}/{gname}')
            for f in files:
                if f in seen:
                    sys.exit(f'{f} is in two groups: {seen[f]} and {(side, gname)}')
                seen[f] = (side, gname)
            files_of[(side, gname)] = files_of.get((side, gname), []) + files
            for s in sides_of(side):
                counts[(s, gname)] = counts.get((s, gname), 0) + sum(code_lines(f) for f in files)
        every = {f for f in glob.glob('agda/**/*.agda', recursive=True)
                 if not f.startswith('agda/old/') and f not in ('agda/All.agda', U + 'All.agda', MU + 'All.agda')
                 and f not in BUNDLES}
        missing = sorted(every - set(seen))
        if missing:
            sys.exit('not in any group:\n  ' + '\n  '.join(missing))

        # units: the two halves of a split module count as one module
        files_of_unit = {}
        for f in every:
            files_of_unit.setdefault(unit(f), []).append(f)
        group_of = {}
        for un, fs in files_of_unit.items():
            gs = {seen[f] for f in fs}
            if len(gs) > 1:
                sys.exit(f'the halves of {un} are in different groups: {sorted(gs)}')
            group_of[un] = gs.pop()
        self.seen, self.counts, self.files_of = seen, counts, files_of
        self.every, self.files_of_unit, self.group_of = every, files_of_unit, group_of
        self.units = set(files_of_unit)
        self.fgraph = {f: imports(f) for f in every}
        self.graph = {un: {unit(g) for f in files_of_unit[un] for g in self.fgraph[f]} - {un}
                      for un in self.units}
        allsides = set(STYLE)
        self.own = {s: {un for un, (side, _) in group_of.items() if s in sides_of(side)} for s in allsides}
        self.infra = {un for un, (side, _) in group_of.items() if side == 'infra'}
        self.reach = {s: reachable(self.own[s], self.graph) for s in allsides}
        self.check()

    def ulines(self, un):
        return sum(code_lines(f) for f in self.files_of_unit[un])

    def lines(self, us):
        return sum(self.ulines(un) for un in us)

    def display(self, un):
        """The name of a unit, and (+ proof/) when it is split."""
        fs = sorted(self.files_of_unit[un], key=is_proof)
        mark = ' (+ proof/)' if len(fs) > 1 else ''
        return f'`{modname(fs[0])}`{mark}'

    def check(self):
        group_of, graph, own, reach = self.group_of, self.graph, self.own, self.reach
        # Infrastructure is language independent: it imports only infrastructure.
        bad = sorted(reachable(self.infra, graph) - self.infra)
        if bad:
            sys.exit('infrastructure imports modules that are not infrastructure:\n  ' + '\n  '.join(bad))
        # The main development does not depend on the preserved untyped one.
        for f in sorted(self.every):
            if not f.startswith(U):
                bad = sorted(g for g in self.fgraph[f] if g.startswith(U))
                if bad:
                    sys.exit(f'{f} imports modules of agda/Untyped/:\n  ' + '\n  '.join(bad))
        # The proofs must be independent: no proof reaches another proof's
        # modules (of either pipeline, the shared rows apart), nor adequacy's,
        # an example or an experiment (adequacy, examples and experiments may
        # use anything).  The graph models with errors may use the graph
        # model's meaning of the primitives, which they extend.
        exp = {un for un, (side, _) in group_of.items() if side in ('uexp', 'examples', 'uexamples')}
        cols = [s for s in STYLE if STYLE[s] in ('den', 'op', 'ck', 'red', 'gerr')]
        prim = {G + 'Prim.agda'}
        for s in cols:
            for t in STYLE:
                if t == s:
                    continue
                bad = reach[s] & (own[t] - own[s])
                if STYLE[s] == 'gerr':
                    bad -= prim
                if bad:
                    sys.exit(f'{s} ({name(s)}) imports {t} ({name(t)}) modules:\n  ' + '\n  '.join(sorted(bad)))
            bad = sorted(reach[s] & exp)
            if bad:
                sys.exit(f'{s} ({name(s)}) imports example or experiment modules:\n  ' + '\n  '.join(bad))
        # The audit surface: every module outside the proof/ directories,
        # reached from the theorem files through modules outside them, and
        # importing none of them (but the theorem files, which cite the
        # proofs).
        thm = set(TYPED['thm'].values()) | set(UNTYPED['thm'].values()) | {ASSURE_THM}
        if thm != {f for f, (side, _) in self.seen.items() if side in ('thm', 'uthm')}:
            sys.exit('the theorem files are not ' + ', '.join(sorted(thm)))
        surface = {f for f in self.every if not is_proof(f) and not f.startswith(MU)}
        self.sgraph = {f: {g for g in self.fgraph[f] if g in surface} for f in surface}
        for f in sorted(surface - thm):
            bad = sorted(g for g in self.fgraph[f] if is_proof(g))
            if bad:
                sys.exit(f'{f}, on the audit surface, imports proof modules:\n  ' + '\n  '.join(bad))
        unreached = sorted(surface - reachable(thm, self.sgraph))
        if unreached:
            sys.exit('outside the proof/ directories but not reached from the theorem files:\n  '
                     + '\n  '.join(unreached))
        self.thm = thm

    def analyze(self, P):
        """The totals of pipeline P: per column and row, the shared modules each
        counts, adequacy's."""
        own, reach, graph, group_of = self.own, self.reach, self.graph, self.group_of
        sides, gerr, adeq, gadeq = P['sides'], P['gerr'], P['adeq'], P['gadeq']
        shared = {un for un, (side, _) in group_of.items() if side in P['shared']}
        by_all = shared.intersection(*(reach[s] for s in sides))
        extra = {s: sorted((shared & reach[s]) - by_all) for s in sides}
        # Adequacy is an add-on to the denotational proof, so shared modules that
        # the denotational proof already counts are not counted again.
        extra[adeq] = sorted((shared & reach[adeq]) - by_all - set(extra[sides[0]]))
        # The graph model with errors is counted as the four are: its own
        # modules and the shared ones it reaches that all four do not; and the
        # graph model's modules it uses (the meaning of the primitives).  Its
        # adequacy is counted as adequacy is: what it adds to its proof.  Where
        # it derives Clos5ᵀ adequacy from the CEK column's simulation, the CEK
        # modules it reaches (and what only they reach) are reported apart.
        den = sides[0]
        extra[gerr] = sorted((shared & reach[gerr]) - by_all)
        borrowed = {gerr: sorted(reach[gerr] & (own[den] - own[gerr]))}
        others = {un for un, (side, row) in group_of.items()
                  if set(sides_of(side)) & set(sides[1:]) and row != 'semantics of the languages'} \
            - own[gerr] - own[gadeq]
        rg = reachable(own[gadeq], graph, avoid=others)
        derived = sorted(reachable(own[gadeq], graph) - rg - self.infra - reach[gerr])
        extra[gadeq] = sorted((shared & rg) - by_all - set(extra[gerr]))
        borrowed[gadeq] = sorted(rg & ((own[den] | own[adeq]) - own[gerr]) - reach[gerr])
        mcols = sides + (gerr,)
        total = {s: 0 for s in mcols}
        cells = {}
        for r in ROWS:
            for s in mcols:
                n = self.counts.get((s, r))
                total[s] += n or 0
                cells[(s, r)] = n
        for s in mcols:
            n = self.lines(extra[s])
            total[s] += n
            cells[(s, EXTRA)] = n if extra[s] else None
        n = self.lines(borrowed[gerr])
        total[gerr] += n
        cells[(gerr, 'prim')] = n
        anames = [r for r in ADEQ_ROWS if any(self.counts.get((s, r)) for s in (adeq, gadeq))]
        adq = {adeq: 0, gadeq: 0}
        for gname in anames:
            for s in (adeq, gadeq):
                adq[s] += self.counts.get((s, gname)) or 0
        for s in (adeq, gadeq):
            adq[s] += self.lines(extra[s])
        adq[gadeq] += self.lines(borrowed[gadeq])
        return dict(P=P, mcols=mcols, total=total, cells=cells, extra=extra, borrowed=borrowed,
                    by_all=by_all, shared=shared, anames=anames, adq=adq, derived=derived)

    def print_pipeline(self, R):
        P, mcols, cells, total = R['P'], R['mcols'], R['cells'], R['total']
        sides, gerr, adeq, gadeq = P['sides'], P['gerr'], P['adeq'], P['gadeq']
        extra, borrowed = R['extra'], R['borrowed']
        print(f'| component{tag(P)} | ' + ' | '.join(label(s) for s in mcols) + ' |')
        print('|---|' + '---:|' * len(mcols))
        for r in ROWS:
            ns = [cells[(s, r)] for s in mcols]
            if any(n is not None for n in ns):
                print(f'| {r} | ' + ' | '.join(bold_min(ns)) + ' |')
        print(f'| {EXTRA} | ' + ' | '.join(bold_min([cells[(s, EXTRA)] for s in mcols])) + ' |')
        print("| the graph model's meaning of the primitives | — | — | — | — | " + str(cells[(gerr, 'prim')]) + ' |')
        print('| **total** | ' + ' | '.join(bold_min([total[s] for s in mcols])) + ' |')
        print()

        reach, infra = self.reach, self.infra
        print(f'| language-independent infrastructure{tag(P)} (not in the totals) | lines | '
              + ' | '.join(f'used by {label(s)}' for s in mcols) + ' |')
        print('|---|---:|' + '---:|' * len(mcols))
        itotal = {s: 0 for s in mcols}
        for side, gname, _ in GROUPS:
            if side == 'infra':
                us = {unit(f) for f in self.files_of[(side, gname)]}
                row = []
                for s in mcols:
                    n = self.lines(un for un in us if un in reach[s])
                    itotal[s] += n
                    row.append(str(n) if n else '—')
                print(f'| {gname} | {self.counts[(side, gname)]} | ' + ' | '.join(row) + ' |')
        print(f'| **total** | {self.lines(infra)} | ' + ' | '.join(str(itotal[s]) for s in mcols) + ' |')
        print()
        print(f"Adequacy uses {self.lines(infra & reach[adeq])} lines of the infrastructure, "
              f"{self.lines(infra & reach[adeq] - reach[sides[0]])} of them not used by the denotational proof.")
        print()
        print(f'| adequacy{tag(P)} (denotational side only) | graph model | graph model with errors |')
        print('|---|---:|---:|')
        for gname in R['anames']:
            print(f'| {gname} | ' + ' | '.join(bold_min([self.counts.get((s, gname)) for s in (adeq, gadeq)])) + ' |')
        ns = [self.lines(extra[s]) if extra[s] else None for s in (adeq, gadeq)]
        print(f'| {EXTRA}, nor by the proof of its model | ' + ' | '.join(bold_min(ns)) + ' |')
        n = self.lines(borrowed[gadeq])
        print(f"| the graph model's modules it uses | — | {n if borrowed[gadeq] else '—'} |")
        print('| **total** | ' + ' | '.join(bold_min([R['adq'][adeq], R['adq'][gadeq]])) + ' |')
        if R['derived']:
            print(f"| the CEK proof it derives Clos5ᵀ adequacy from (not in the total) | — | "
                  f"{self.lines(R['derived'])} |")
            print()
            print('The CEK modules that adequacy with errors reaches only to derive Clos5ᵀ adequacy: '
                  + ', '.join(f'{self.display(un)} ({self.ulines(un)})' for un in R['derived']) + '.')
        print()
        exps = [(side, gname) for side, gname, _ in GROUPS if side == P['exp']]
        if exps:
            print(f'| experiment{tag(P)} (not in the totals) | lines |')
            print('|---|---:|')
            for side, gname in exps:
                print(f'| {gname} | {self.counts[(side, gname)]} |')
            print()
        self.print_audit(P)
        self.print_modules(R)

    def print_audit(self, P):
        """The audit surface of each style: the modules outside the proof/
        directories that its theorem file reaches, by kind."""
        seen, sgraph = self.seen, self.sgraph
        shared_infra = ('abstract binding trees', 'syntax lemmas (renaming, scoping, uses, substitution), list lookups',
                        'base types, logical equivalence',
                        'typed indices, lookup in typed lists, vectors (collecting, selecting, projecting)')

        def kind(f):
            side, gname = seen[f]
            if side in ('thm', 'uthm'):
                return 'statements'
            if side in ('shared', 'ushared') or (side == 'infra' and gname in shared_infra):
                return 'shared'
            return 'semantics'
        T = P['thm']
        cols = P['sides'] + (P['adeq'], P['gerr'])
        sreach = {s: reachable({T[s]}, sgraph) for s in cols}

        def flines(fs):
            return sum(code_lines(f) for f in fs)
        sh = {s: {f for f in sreach[s] if kind(f) == 'shared'} for s in cols}
        print(f'| audit surface{tag(P)} (not in the totals) | lines | '
              + ' | '.join(f'read for {label(s)}' for s in cols) + ' |')
        print('|---|---:|' + '---:|' * len(cols))
        print(f'| languages, compiler passes, syntax, base types (shared) | {flines(set().union(*sh.values()))} | '
              + ' | '.join(str(flines(sh[s])) for s in cols) + ' |')
        SEMS = {'den': 'domain, operators, semantics of each language',
                'op': 'small-step machines, transition systems',
                'ck': 'clocked interpreters, results',
                'red': 'reduction semantics, machines of the first-order languages, transition systems',
                'gerr': 'domain, error-propagating operators, semantics of each language'}
        sem_files = {s: {f for f in sreach[s] if kind(f) == 'semantics'} for s in cols}
        for s in P['sides'] + (P['gerr'],):
            fs = sem_files[s]
            print(f'| {name(s)}: {SEMS[STYLE[s]]} | {flines(fs)} | '
                  + ' | '.join(str(flines(sem_files[t] & fs)) if sem_files[t] & fs else '—' for t in cols) + ' |')
        thm = set(T.values())
        for s in cols:
            print(f'| {name(s)}: theorem statements | {code_lines(T[s])} | '
                  + ' | '.join(str(code_lines(T[s])) if t == s else '—' for t in cols) + ' |')
        tot = {s: flines(sreach[s] - (thm - {T[s]})) for s in cols}
        alls = set().union(*(sreach[s] for s in cols))
        styles = [s for s in cols if s != P['adeq']]
        low = min(tot[s] for s in styles)
        print(f'| **total** | {flines(alls)} | '
              + ' | '.join(f'**{tot[s]}**' if s != P['adeq'] and tot[s] == low else str(tot[s]) for s in cols) + ' |')
        print()
        rho = [f for f in sreach[P['adeq']] if f in thm and f != T[P['adeq']]]
        if rho:
            print('The adequacy statements also use ρ₀ from the denotational ones '
                  f'({", ".join(f[len("agda/"):] for f in rho)}), not counted in its column.')
            print()

    def print_modules(self, R):
        P, reach = R['P'], self.reach
        users_of = P['sides'] + (P['adeq'], P['gerr'], P['gadeq'])
        print(f'| shared module{tag(P)} | lines | used by |')
        print('|---|---:|---|')
        for un in sorted(R['shared'], key=lambda x: self.display(x)):
            users = [name(s) for s in users_of if un in reach[s]]
            if not users:
                continue
            who = 'all four proofs' if un in R['by_all'] else ', '.join(users)
            print(f'| {self.display(un)} | {self.ulines(un)} | {who} |')
        print()
        print(f'| infrastructure module{tag(P)} | lines | used by |')
        print('|---|---:|---|')
        for un in sorted(self.infra, key=lambda x: self.display(x)):
            users = [name(s) for s in users_of if un in reach[s]]
            print(f'| {self.display(un)} | {self.ulines(un)} | {", ".join(users) or "no proof"} |')
        print()

        def mods(us):
            return ', '.join(f'{self.display(un)} ({self.ulines(un)})' for un in us) or 'none'
        print(f"Shared by all four proofs, not counted: {len(R['by_all'])} modules, {self.lines(R['by_all'])} lines.")
        for s in users_of:
            print(f'Counted in {name(s)}: {mods(R["extra"][s])}.')
        for s in (P['gerr'], P['gadeq']):
            print(f'Of the graph model, counted in {name(s)}: {mods(R["borrowed"][s])}.')
        unused = sorted(un for un in R['shared'] if not any(un in reach[s] for s in users_of)
                        and self.group_of[un][0] in P['shared'][-1:])
        if unused:
            print(f'Shared but used by no proof: {mods(unused)}.')
        ex = 'examples' if P is TYPED else 'uexamples'
        print(f"Examples, not counted: {self.counts[(ex, 'examples')]} lines.")
        print()
        print("Module (+ proof/): the definitions are on the audit surface, the lemmas "
              "in its proof/ half; the lines are those of both.")
        print()

    def errors_infra(self, P):
        """The infrastructure each graph model reaches, by group, and what they
        share: the semantics and the correctness proofs (without adequacy), and
        then what adequacy adds, in each model."""
        reach = self.reach
        den, gerr, adeq, gadeq = P['sides'][0], P['gerr'], P['adeq'], P['gadeq']
        rd = reach[adeq] - reach[den]
        ra = reach[gadeq] - reach[gerr]
        print(f'| infrastructure group{tag(P)} | lines | graph model | graph model with errors | both '
              '| adequacy adds: graph model | adequacy adds: graph model with errors |')
        print('|---|---:|---:|---:|---:|---:|---:|')
        tot = [0] * 6
        for side, gname, _ in GROUPS:
            if side == 'infra':
                us = {unit(f) for f in self.files_of[(side, gname)]}
                row = [self.lines(us),
                       self.lines(un for un in us if un in reach[den]),
                       self.lines(un for un in us if un in reach[gerr]),
                       self.lines(un for un in us if un in reach[den] and un in reach[gerr]),
                       self.lines(un for un in us if un in rd),
                       self.lines(un for un in us if un in ra)]
                if any(row[1:]):
                    tot = [t + r for t, r in zip(tot, row)]
                    print(f'| {gname} | {row[0]} | ' + ' | '.join(str(r) if r else '—' for r in row[1:]) + ' |')
        print('| **total** | ' + ' | '.join(str(t) for t in tot) + ' |')
        ops = {unit(f) for f in self.files_of[('infra', 'graph model: its operators')]}
        used = sorted(ops & (reach[gerr] | reach[gadeq]))
        print()
        print("The graph model with errors reuses these modules of the graph model's operators: "
              + ', '.join(f'`{modname(un)}` ({self.ulines(un)})' for un in used) + '.')
        print()


def assurance(c):
    """The assurance of the typed pipeline (not in the totals, nor in the
    comparison): what checks that X86ᵀ is faithful to untyped X86."""
    print('| assurance (not in the totals) | lines |')
    print('|---|---:|')
    for side, gname, _ in GROUPS:
        if side == 'assure':
            print(f'| {gname} | {c.counts[(side, gname)]} |')
    print(f'| the statements (`Theorems/X86Erasure.agda`) | {code_lines(ASSURE_THM)} |')
    print()


def compare(c, T, Un):
    """The typed pipeline against the untyped one, column by column (the lower
    of the two is bold in each column); the totals with and without cast
    insertion, which the untyped pipeline does not have."""
    cols = list(zip(T['mcols'], Un['mcols']))
    print('| typed against untyped | '
          + ' | '.join(f'{label(t)}: untyped | {label(t)}: typed' for t, _ in cols) + ' |')
    print('|---|' + '---:|' * (2 * len(cols)))
    rows = ROWS + [EXTRA, 'prim']
    for r in rows:
        cells = []
        for t, un in cols:
            cells += bold_min([Un['cells'].get((un, r)), T['cells'].get((t, r))])
        if any(x != '—' for x in cells):
            rname = "the graph model's meaning of the primitives" if r == 'prim' else r
            print(f'| {rname} | ' + ' | '.join(cells) + ' |')
    cells = []
    for t, un in cols:
        cells += bold_min([Un['total'][un], T['total'][t]])
    print('| **total** | ' + ' | '.join(cells) + ' |')
    cells = []
    for t, un in cols:
        cells += bold_min([Un['total'][un], T['total'][t] - (T['cells'].get((t, 'cast insertion')) or 0)])
    print('| **total without cast insertion** | ' + ' | '.join(cells) + ' |')
    print()
    print('| adequacy, typed against untyped | graph model: untyped | graph model: typed '
          '| graph model with errors: untyped | graph model with errors: typed |')
    print('|---|---:|---:|---:|---:|')
    print('| **total** | ' + ' | '.join(bold_min([Un['adq'][UNTYPED['adeq']], T['adq'][TYPED['adeq']]])
                                       + bold_min([Un['adq'][UNTYPED['gadeq']], T['adq'][TYPED['gadeq']]])) + ' |')
    print()


# --- the ISWIMμ pilot ------------------------------------------------------

# the rows of the pilot, and the files of the typed pipeline it compares
# with, for the graph model ('den') and the CEK machines ('op'): the
# semantics of each language (its definitions and lemmas), what the
# languages share, the lemmas the passes share, the passes from enclose to
# select, and the composition (row, typed graph, typed CEK, μ graph, μ CEK).
# Monᵀ and Monμ have no semantics of their own (their embedding into Clos5).
# The typed graph model's Ops has project (with fun₂/fun₄) and the tables,
# the pilot's only the tables; the typed CEK lemmas Common collect a tuple's
# values with its length equation.


def mu_sem(x, typed_graph_lemmas=False, mu_graph_lemmas=False):
    """The row of the semantics of language x."""
    return (f'semantics: {x}',
            [G + f'Typed/{x}.agda'] + ([GP + f'Typed/{x}.agda'] if typed_graph_lemmas else []),
            [O + f'Typed/{x}.agda'],
            [MU + f'Semantics/Graph/{x}.agda'] + ([MUP + f'Semantics/Graph/{x}.agda'] if mu_graph_lemmas else []),
            [MU + f'Semantics/CEK/{x}.agda'])


def mu_pass(row, graph, cek):
    """The row of a pass, whose proofs have the same names in both pipelines."""
    return (row, [GC + g for g in graph], [OC + o for o in cek],
            [MUP + 'Correctness/Graph/' + g for g in graph], [MUP + 'Correctness/CEK/' + o for o in cek])


MU_DELAY = ['Rel', 'Preserve', 'Reflect', 'Correct']
MU_ROWS = [
    mu_sem('ISWIM'),
    mu_sem('Clos2', True, True),
    mu_sem('Clos3', True, True),
    mu_sem('Clos4', True, True),
    mu_sem('Clos5', True, True),
    mu_sem('Imp'),
    mu_sem('CFG', True, True),
    mu_sem('X86'),
    ('what the languages share: project (typed only), tables (`Ops`)',
     [G + 'Typed/Ops.agda', GP + 'Typed/Ops.agda'], [],
     [MU + 'Semantics/Graph/Ops.agda', MUP + 'Semantics/Graph/Ops.agda'], []),
    ('lemmas shared by the passes (`Common`, `Clos5Common`)', [], [OC + 'Common.agda', OC + 'Clos5Common.agda'],
     [], [MUP + 'Correctness/CEK/Clos5Common.agda']),
    mu_pass('CC: enclose', ['EncloseCorrect.agda'], ['EncloseSim.agda']),
    mu_pass('CC: optimize', ['OptimizeCorrect.agda'], ['OptimizeSim.agda']),
    mu_pass('CC: concretize', ['ConcretizeCorrect.agda'], ['ConcretizeSim.agda']),
    mu_pass('CC: delay', ['Delay' + x + '.agda' for x in MU_DELAY], ['DelaySim.agda']),
    mu_pass('CC: globalize', ['GlobalizeCorrect.agda'], ['GlobalizeSim.agda']),
    mu_pass('rco', ['RCOCorrect.agda'], ['RCOSim.agda']),
    mu_pass('lift locals', ['LiftLocalsCorrect.agda'], ['LiftLocalsSim.agda']),
    mu_pass('explicate control', ['ExplicateCorrect.agda'], ['ExplicateSim.agda']),
    mu_pass('select instructions', ['SelectCorrect.agda'], ['SelectSim.agda']),
    mu_pass('composition', ['CompilerCorrect.agda'], ['PipelineSim.agda']),
]
MU_SHARED = ([L + 'Typed/' + x + '.agda'
              for x in ('Type', 'ISWIM', 'Clos2', 'Clos3', 'Clos4', 'Clos5', 'Mon', 'Imp', 'CFG', 'X86')]
             + [C + x + '.agda' for x in ('Enclose', 'Optimize', 'Concretize', 'Delay', 'Globalize', 'RCO',
                                          'LiftLocals', 'Explicate', 'Select', 'Pipeline')])
MU_INFRA = [W + 'VecUtil.agda', W + 'VecSelect.agda', WP + 'VecSelect.agda', WP + 'Lookup.agda']


def mu_check(c):
    """The pilot's columns are independent of each other and of the proofs of
    either pipeline (they may use what both pipelines share), and its
    infrastructure imports only infrastructure."""
    sides = ('mu-den', 'mu-op', 'mu-ck')
    own = {s: {un for un, (side, _) in c.group_of.items() if s in sides_of(side)} for s in sides}
    reach = {s: reachable(own[s], c.graph) for s in sides}
    typed, untyped = set(TYPED['sides']) | {'gerr', 'adeq', 'gadeq'}, set(UNTYPED['sides']) | {'ugerr', 'uadeq', 'ugadeq'}
    for s in sides:
        bad = set()
        for un in reach[s]:
            side = c.group_of[un][0]
            if (set(sides_of(side)) & set(sides) and s not in sides_of(side)) \
                    or side in ('mu-adeq', 'mu-noerr', 'mu-examples'):
                bad.add(un)
            ss = set(sides_of(side))
            if ss <= set(STYLE) and not (ss & typed and ss & untyped):
                bad.add(un)
        if bad:
            sys.exit(f'{s} imports modules of another proof:\n  ' + '\n  '.join(sorted(bad)))
    minfra = {un for un, (side, _) in c.group_of.items() if side == 'mu-infra'}
    bad = sorted(reachable(minfra, c.graph) - minfra - c.infra)
    if bad:
        sys.exit("the pilot's infrastructure imports modules that are not infrastructure:\n  " + '\n  '.join(bad))


def mu_report(c, T):
    """The ISWIMμ pilot against the typed pipeline, row by row, in the graph
    model and the CEK machines; and against the totals of the main table
    without simplify and cast insertion."""

    def n(fs):
        return sum(code_lines(f) for f in fs) if fs else None

    def cell(x):
        return '—' if x is None else str(x)
    print('| ISWIMμ pilot against the typed pipeline | graph model: typed | graph model: μ '
          '| CEK: typed | CEK: μ |')
    print('|---|---:|---:|---:|---:|')
    tot = [0, 0, 0, 0]
    for row, gt, ot, gm, om in MU_ROWS:
        ns = [n(gt), n(gm), n(ot), n(om)]
        tot = [t + (x or 0) for t, x in zip(tot, ns)]
        print(f'| {row} | ' + ' | '.join(cell(x) for x in ns) + ' |')
    print('| **total** | ' + ' | '.join(str(t) for t in tot) + ' |')
    # the main table's totals of the typed pipeline, without simplify and
    # cast insertion: they also count untyped ISWIM's semantics and the
    # primitives' (which simplify needs), the untyped ISWIM machine and the
    # framework instances, and the observations
    cells, total = T['cells'], T['total']
    main_tot = {s: total[s] - (cells[(s, 'simplify')] or 0) - (cells[(s, 'cast insertion')] or 0)
                for s in ('den', 'op')}
    print(f"| the main table's total, without simplify and cast insertion | {main_tot['den']} | — "
          f"| {main_tot['op']} | — |")
    print()
    print('| graph-model delay, by module | typed | μ |')
    print('|---|---:|---:|')
    for x in MU_DELAY:
        print(f'| `Delay{x}` | {code_lines(GC + "Delay" + x + ".agda")} '
              f'| {code_lines(MUP + "Correctness/Graph/Delay" + x + ".agda")} |')
    print()
    print('| not counted in the rows | typed | μ |')
    print('|---|---:|---:|')
    mush = [f for f in c.every if c.seen[f][0] == 'mu-shared']
    print(f'| languages and passes (ISWIM … X86, enclose … select, and their composition) | {n(MU_SHARED)} | {n(mush)} |')
    mui = [f for f in c.every if c.seen[f][0] == 'mu-infra']
    print(f'| infrastructure: vectors and lookup lemmas (`VecUtil`, `VecSelect`, `proof/Framework/Lookup`) '
          f'against heterogeneous vectors (`Mu/Framework/AllUtil`, `AllProp`) '
          f'| {n(MU_INFRA)} | {n(mui)} |')
    mex = [f for f in c.every if c.seen[f][0] == 'mu-examples']
    print(f'| examples | — | {n(mex)} |')
    print()


# the clocked interpreters of the pilot ('mu-ck') against the typed
# pipeline's, row by row: the interpreter of each language, the values
# they share and the value relations, and each pass.  The typed column is
# without simplify and cast insertion, which the pilot does not have.
MU_CK_ROWS = [
    ('semantics: ISWIM', [F + 'Typed/ISWIM.agda'], [MU + 'Semantics/Interp/ISWIM.agda']),
    ('semantics: Clos2', [F + 'Typed/Clos2.agda'], [MU + 'Semantics/Interp/Clos2.agda']),
    ('semantics: Clos3', [F + 'Typed/Clos3.agda'], [MU + 'Semantics/Interp/Clos3.agda']),
    ('semantics: Clos4', [F + 'Typed/Clos4.agda'], [MU + 'Semantics/Interp/Clos4.agda']),
    ('semantics: Clos5 (with the lemmas about Mon\'s embedding)', [F + 'Typed/Clos5.agda', FP + 'Typed/Clos5.agda'],
     [MU + 'Semantics/Interp/Clos5.agda', MUP + 'Semantics/Interp/Clos5.agda']),
    ('semantics: Imp', [F + 'Typed/Imp.agda'], [MU + 'Semantics/Interp/Imp.agda']),
    ('semantics: CFG', [F + 'Typed/CFG.agda'], [MU + 'Semantics/Interp/CFG.agda']),
    ('semantics: X86', [F + 'Typed/X86.agda'], [MU + 'Semantics/Interp/X86.agda']),
    ('semantics: values (`Values`)', [F + 'Typed/Values.agda'], [MU + 'Semantics/Interp/Values.agda']),
    ('semantics: value relations (`Rel`)', [FP + 'Typed/Rel.agda'], [MUP + 'Semantics/Interp/Rel.agda']),
    ('CC: enclose', [FC + 'EncloseFuel.agda'], [MUP + 'Correctness/Interp/EncloseFuel.agda']),
    ('CC: optimize', [FC + 'OptimizeFuel.agda'], [MUP + 'Correctness/Interp/OptimizeFuel.agda']),
    ('CC: concretize', [FC + 'ConcretizeFuel.agda'], [MUP + 'Correctness/Interp/ConcretizeFuel.agda']),
    ('CC: delay', [FC + 'DelayFuel.agda'], [MUP + 'Correctness/Interp/DelayFuel.agda']),
    ('CC: globalize', [FC + 'GlobalizeFuel.agda'], [MUP + 'Correctness/Interp/GlobalizeFuel.agda']),
    ('rco', [FC + 'RCOFuel.agda'], [MUP + 'Correctness/Interp/RCOFuel.agda']),
    ('lift locals', [FC + 'LiftLocalsFuel.agda'], [MUP + 'Correctness/Interp/LiftLocalsFuel.agda']),
    ('explicate control', [FC + 'ExplicateFuel.agda'], [MUP + 'Correctness/Interp/ExplicateFuel.agda']),
    ('select instructions', [FC + 'SelectFuel.agda'], [MUP + 'Correctness/Interp/SelectFuel.agda']),
]


def mu_ck_report(c):
    """The pilot's clocked interpreters against the typed pipeline's."""

    def n(fs):
        return sum(code_lines(f) for f in fs) if fs else None

    def cell(x):
        return '—' if x is None else str(x)
    print('| ISWIMμ pilot against the typed pipeline | interpreter: typed | interpreter: μ |')
    print('|---|---:|---:|')
    tot = [0, 0]
    for row, ft, fm in MU_CK_ROWS:
        ns = [n(ft), n(fm)]
        tot = [t + (x or 0) for t, x in zip(tot, ns)]
        print(f'| {row} | ' + ' | '.join(cell(x) for x in ns) + ' |')
    print('| **total** | ' + ' | '.join(str(t) for t in tot) + ' |')
    comp = [n([FC + 'CompilerFuel.agda']), n([MUP + 'Correctness/Interp/CompilerFuel.agda'])]
    tot = [t + x for t, x in zip(tot, comp)]
    print('| composition | ' + ' | '.join(cell(x) for x in comp) + ' |')
    print('| **total with the composition** | ' + ' | '.join(str(t) for t in tot) + ' |')
    print()


# --- the pilot's reduction column ---------------------------------------------
# rows (name, typed files, μ files), like for like: the typed reduction
# column without simplify and cast insertion (and without the reduction
# semantics of untyped ISWIM, which only their proofs use)
MU_RED_ROWS = [
    ('semantics: ' + x, [RD + 'Typed/' + x + '.agda', RP + 'Typed/' + x + '.agda'],
     [MU + 'Semantics/Reduction/' + x + '.agda', MUP + 'Semantics/Reduction/' + x + '.agda'])
    for x in ('ISWIM', 'Clos2', 'Clos3', 'Clos4', 'Clos5')] + [
    ('semantics: transition systems (shared)', [RD + 'Smallstep.agda'], [RD + 'Smallstep.agda']),
    ('semantics: machines of Clos5, Imp, CFG, X86 (the CEK column\'s)',
     [O + 'Typed/' + x + '.agda' for x in ('Clos5', 'Imp', 'CFG', 'X86')],
     [MU + 'Semantics/CEK/' + x + '.agda' for x in ('Clos5', 'Imp', 'CFG', 'X86')]),
    ('semantics: the CEK framework at this compiler\'s observations (shared)',
     [O + 'Smallstep.agda', OP + 'Smallstep.agda', OP + 'Simulation.agda'],
     [O + 'Smallstep.agda', OP + 'Smallstep.agda', OP + 'Simulation.agda']),
    ('CC: enclose', [RC + 'EncloseRed.agda'], [MUP + 'Correctness/Reduction/EncloseRed.agda']),
    ('CC: optimize', [RC + 'OptimizeRed.agda'], [MUP + 'Correctness/Reduction/OptimizeRed.agda']),
    ('CC: concretize', [RC + 'ConcretizeRed.agda'], [MUP + 'Correctness/Reduction/ConcretizeRed.agda']),
    ('CC: delay', [RC + 'DelayRed.agda'], [MUP + 'Correctness/Reduction/DelayRed.agda']),
    ('CC: globalize', [RC + 'GlobalizeRed.agda'], [MUP + 'Correctness/Reduction/GlobalizeRed.agda']),
    ('rco', [RC + 'RCORed.agda'], [MUP + 'Correctness/Reduction/RCORed.agda']),
    ('lift locals', [RC + 'LiftLocalsRed.agda'], [MUP + 'Correctness/Reduction/LiftLocalsRed.agda']),
    ('explicate control (the CEK column\'s)', [OC + 'ExplicateSim.agda'], [MUP + 'Correctness/CEK/ExplicateSim.agda']),
    ('select instructions (the CEK column\'s)', [OC + 'SelectSim.agda'], [MUP + 'Correctness/CEK/SelectSim.agda']),
]
MU_RED_COMP = ([RC + 'PipelineRed.agda'], [MUP + 'Correctness/Reduction/PipelineRed.agda'])
# what the pilot's reduction column shares with its CEK column
MU_RED_SHARED = ([MU + 'Semantics/CEK/' + x + '.agda' for x in ('Clos5', 'Imp', 'CFG', 'X86')]
                 + [MUP + 'Correctness/CEK/' + x + 'Sim.agda' for x in ('Explicate', 'Select')])


def mu_red_check(c):
    """As mu_check, for the pilot's reduction column: it reaches no module of
    another of the pilot's columns (those it shares with one, 'mu-op+mu-red',
    apart) nor of a proof of either pipeline (what both share apart), and its
    infrastructure imports only infrastructure."""
    shared = {unit(f) for f in MU_RED_SHARED}
    own = {un for un, (side, _) in c.group_of.items() if 'mu-red' in sides_of(side)} | shared
    typed, untyped = set(TYPED['sides']) | {'gerr', 'adeq', 'gadeq'}, set(UNTYPED['sides']) | {'ugerr', 'uadeq', 'ugadeq'}
    bad = set()
    for un in reachable(own, c.graph):
        side = c.group_of[un][0]
        ss = set(sides_of(side))
        if side.startswith('mu-') and 'mu-red' not in ss and un not in shared \
                and side not in ('mu-shared', 'mu-infra', 'mu-rinfra'):
            bad.add(un)
        if ss <= set(STYLE) and not (ss & typed and ss & untyped):
            bad.add(un)
    if bad:
        sys.exit('mu-red imports modules of another proof:\n  ' + '\n  '.join(sorted(bad)))
    rinfra = {un for un, (side, _) in c.group_of.items() if side in ('mu-infra', 'mu-rinfra')}
    bad = sorted(reachable(rinfra, c.graph) - rinfra - c.infra)
    if bad:
        sys.exit("the pilot's reduction infrastructure imports modules that are not infrastructure:\n  "
                 + '\n  '.join(bad))


def mu_red_report(c):
    """The pilot's reduction column against the typed one, row by row."""

    def n(fs):
        fs = [f for f in fs if os.path.exists(f)]
        return sum(code_lines(f) for f in fs) if fs else None

    def cell(x):
        return '—' if x is None else str(x)
    print('| ISWIMμ pilot against the typed pipeline: reduction | typed | μ |')
    print('|---|---:|---:|')
    tot = [0, 0]
    for row, t, m in MU_RED_ROWS:
        ns = [n(t), n(m)]
        tot = [a + (x or 0) for a, x in zip(tot, ns)]
        print(f'| {row} | ' + ' | '.join(cell(x) for x in ns) + ' |')
    print('| **total** | ' + ' | '.join(str(x) for x in tot) + ' |')
    print('| composition | '
          + ' | '.join(cell(n(fs)) for fs in MU_RED_COMP) + ' |')
    print('| **total with the composition** | '
          + ' | '.join(str(x + n(fs)) for x, fs in zip(tot, MU_RED_COMP)) + ' |')
    T = c.analyze(TYPED)
    main = T['total']['red'] - (T['cells'][('red', 'simplify')] or 0) - (T['cells'][('red', 'cast insertion')] or 0)
    print(f"| the main table's total, without simplify and cast insertion | {main} | — |")
    print()
    print('| reduction: not counted in the rows | typed | μ |')
    print('|---|---:|---:|')
    print(f'| reduction of vectors (`ReductionVec`) against heterogeneous vectors (`Mu/Framework/ReductionAll`) '
          f'| {n([W + "ReductionVec.agda", WP + "ReductionVec.agda"])} | {n([MU + "Framework/ReductionAll.agda"])} |')
    print()


# --- the pilot's main table: the four styles against each other -----------

MU_SIDES = ('mu-den', 'mu-op', 'mu-ck', 'mu-red')
MU_LABELS = {'mu-den': 'denotational: graph model', 'mu-op': 'CEK machine + simulation',
             'mu-ck': 'clocked interpreter + value relations', 'mu-red': 'reduction semantics + simulation',
             'mu-adeq': 'adequacy'}
MU_BORROWED = "the typed pipeline's modules it reuses (meaning of the primitives, framework instances)"


def mu_analyze(c):
    """The pilot's counts, as analyze's for a pipeline: each column's rows, the
    shared modules (languages, passes, the primitives, the observations) it
    reaches that the four do not all reach, and the modules of the typed
    pipeline it reuses (the meaning of the primitives, the instances of the
    frameworks at this compiler's observations), counted where they are used;
    adequacy as an add-on to the graph model."""
    cols = MU_SIDES + ('mu-adeq',)
    own = {s: {un for un, (side, _) in c.group_of.items() if s in sides_of(side)} for s in cols}
    reach = {s: reachable(own[s], c.graph) for s in cols}
    shared = {un for un, (side, _) in c.group_of.items() if side in ('shared', 'mu-shared')}
    by_all = shared.intersection(*(reach[s] for s in MU_SIDES))
    extra = {s: (shared & reach[s]) - by_all for s in MU_SIDES}
    extra['mu-adeq'] = (shared & reach['mu-adeq']) - by_all - extra['mu-den']
    minfra = {un for un, (side, _) in c.group_of.items() if side in ('mu-infra', 'mu-rinfra')}

    def borrowed_of(s):
        return {un for un in reach[s] if not c.group_of[un][0].startswith('mu-')
                and un not in c.infra and un not in shared}
    borrowed = {s: borrowed_of(s) for s in MU_SIDES}
    borrowed['mu-adeq'] = borrowed_of('mu-adeq') - borrowed['mu-den']
    total = {}
    for s in cols:
        rows = ROWS if s != 'mu-adeq' else [g for _, g, _ in GROUPS]
        total[s] = (sum(c.counts.get((s, r)) or 0 for r in dict.fromkeys(rows))
                    + c.lines(extra[s]) + c.lines(borrowed[s]))
    return dict(own=own, reach=reach, extra=extra, borrowed=borrowed, total=total, by_all=by_all,
                minfra=minfra)


def mu_main(c, T):
    """The four styles against each other on the pilot, in the shape of the
    main table; then adequacy, the no-error lemmas and the infrastructure
    by use; then the pilot against the typed pipeline, per style."""
    M = mu_analyze(c)
    print('| component (ISWIMμ pilot) | ' + ' | '.join(MU_LABELS[s] for s in MU_SIDES) + ' |')
    print('|---|' + '---:|' * len(MU_SIDES))
    for r in ROWS:
        ns = [c.counts.get((s, r)) for s in MU_SIDES]
        if any(n is not None for n in ns):
            print(f'| {r} | ' + ' | '.join(bold_min(ns)) + ' |')
    print(f'| {EXTRA} | ' + ' | '.join(bold_min([c.lines(M["extra"][s]) or None for s in MU_SIDES])) + ' |')
    print(f'| {MU_BORROWED} | ' + ' | '.join(bold_min([c.lines(M["borrowed"][s]) or None for s in MU_SIDES])) + ' |')
    print('| **total** | ' + ' | '.join(bold_min([M['total'][s] for s in MU_SIDES])) + ' |')
    print()
    mush = {un for un, (side, _) in c.group_of.items() if side == 'mu-shared'}
    print(f"Shared by all four, not counted: the pilot's languages and passes ({c.lines(mush & M['by_all'])} lines) "
          f"and {c.lines(M['by_all'] - mush)} lines of the typed pipeline's (the primitives, registers).")
    for s in MU_SIDES:
        if M['extra'][s] or M['borrowed'][s]:
            print(f'Counted in {MU_LABELS[s]}: '
                  + ', '.join(f'{c.display(un)} ({c.ulines(un)})' for un in sorted(M['extra'][s] | M['borrowed'][s])) + '.')
    print()

    # adequacy, against the typed pipeline's (plain graph model)
    TA = TYPED['adeq']
    rows = [('ISWIM', 'ISWIM: the source machine (typed: untyped ISWIM\'s, shared with the untyped pipeline)', 'ISWIM'),
            ('Clos5', 'Clos5: the Clos5 machine (typed: with the values shared with X86ᵀ)', None),
            ('X86ᵀ', 'X86: the target machine, direct (μ: with the values, as typed Clos5\'s)', 'X86'),
            ('well-formedness of compiled programs', 'well-formedness of compiled programs',
             'well-formedness of compiled programs'),
            ('end to end', 'end to end', 'end to end')]
    print('| adequacy of the graph model (reported separately) | typed pipeline | ISWIMμ pilot |')
    print('|---|---:|---:|')
    for tr, label_, mr in rows:
        print(f'| {label_} | ' + ' | '.join(bold_min([c.counts.get((TA, tr)), c.counts.get(('mu-adeq', mr)) if mr else None])) + ' |')
    print(f'| {EXTRA}, nor by the graph model | '
          + ' | '.join(bold_min([c.lines(T['extra'][TA]) or None, c.lines(M['extra']['mu-adeq']) or None])) + ' |')
    print(f"| {MU_BORROWED.replace('it reuses', 'μ reuses')}, nor by the graph model | — | "
          f"{c.lines(M['borrowed']['mu-adeq']) or '—'} |")
    print('| **total** | ' + ' | '.join(bold_min([T['adq'][TA], M['total']['mu-adeq']])) + ' |')
    print()
    print('Counted in μ adequacy: '
          + ', '.join(f'{c.display(un)} ({c.ulines(un)})'
                      for un in sorted(M['extra']['mu-adeq'] | M['borrowed']['mu-adeq'])) + '.')
    print()
    print('| no-error lemmas (not in any total) | lines |')
    print('|---|---:|')
    tot = 0
    for side, gname, _ in GROUPS:
        if side == 'mu-noerr':
            tot += c.counts[(side, gname)]
            print(f'| {gname} | {c.counts[(side, gname)]} |')
    print(f'| **total** | {tot} |')
    print()

    # infrastructure by use
    cols = MU_SIDES + ('mu-adeq',)
    print('| language-independent infrastructure (ISWIMμ pilot, not in the totals) | lines | '
          + ' | '.join(f'used by {MU_LABELS[s]}' for s in cols) + ' |')
    print('|---|---:|' + '---:|' * len(cols))
    itotal = {s: 0 for s in cols}
    seen_groups = []
    for side, gname, _ in GROUPS:
        if side in ('infra', 'mu-infra', 'mu-rinfra') and (side, gname) not in seen_groups:
            seen_groups.append((side, gname))
            us = {unit(f) for f in c.files_of[(side, gname)]}
            row = []
            for s in cols:
                n = c.lines(un for un in us if un in M['reach'][s] and (s != 'mu-adeq' or un not in M['reach']['mu-den']))
                itotal[s] += n
                row.append(str(n) if n else '—')
            if any(r != '—' for r in row):
                name_ = gname + (' (the pilot\'s)' if side != 'infra' else '')
                print(f'| {name_} | {c.lines(us)} | ' + ' | '.join(row) + ' |')
    print('| **total** | — | ' + ' | '.join(str(itotal[s]) for s in cols) + ' |')
    print()
    print('Adequacy\'s column counts only the infrastructure that the graph model does not use.')
    print()

    # the pilot against the typed pipeline, per style
    cells, total = T['cells'], T['total']
    print('| per style (secondary) | graph model | CEK | interpreter | reduction |')
    print('|---|---:|---:|---:|---:|')
    tt = [total[s] - (cells[(s, 'simplify')] or 0) - (cells[(s, 'cast insertion')] or 0) for s in TYPED['sides']]
    print('| typed pipeline, main table total without simplify and cast insertion | ' + ' | '.join(map(str, tt)) + ' |')
    print('| ISWIMμ pilot, total | ' + ' | '.join(str(M['total'][s]) for s in MU_SIDES) + ' |')
    print('| typed pipeline: delay | ' + ' | '.join(str(cells[(s, 'CC: delay')]) for s in TYPED['sides']) + ' |')
    print('| ISWIMμ pilot: delay | ' + ' | '.join(str(c.counts[(s, 'CC: delay')]) for s in MU_SIDES) + ' |')
    print()


def main():
    c = Count()
    mu_check(c)
    mu_red_check(c)
    T, Un = c.analyze(TYPED), c.analyze(UNTYPED)
    if '--mu-detail' in sys.argv[1:]:
        print('## The ISWIMμ pilot against the typed pipeline, row by row')
        print()
        mu_report(c, T)
        mu_ck_report(c)
        mu_red_report(c)
        return
    if '--mu' in sys.argv[1:]:
        print('## The ISWIMμ pilot')
        print()
        mu_main(c, T)
        return
    if '--untyped' in sys.argv[1:]:
        print(f'## The {UNTYPED["name"]}')
        print()
        c.print_pipeline(Un)
        c.errors_infra(UNTYPED)
        return
    c.print_pipeline(T)
    c.errors_infra(TYPED)
    compare(c, T, Un)
    assurance(c)


if __name__ == '__main__':
    main()
