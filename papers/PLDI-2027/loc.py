#!/usr/bin/env python3
"""Count code lines of the four compiler-correctness proofs, and of the
audit surface.

Run from the repository root:  python3 papers/PLDI-2027/loc.py

A code line is a line that is not blank, not a comment ({- -} blocks,
-- line comments) and not part of an import statement (`import` or
`open import`, with its continuation lines): imports depend on how
finely a development is split into modules, not on its content.  Every .agda file under agda/ (except agda/old/ and
All.agda) must belong to exactly one group; the script fails otherwise,
so new modules cannot go uncounted.  A group of the interpreter side may
have no files yet (a pass not yet proved); it is shown as —.

The code is split into an audit surface (agda/Theorems/, the public
theorem statements, and the definitions they use, everywhere outside
agda/proof/) and agda/proof/, which need not be read to trust the
results.  A module that mixes definitions and lemmas is split in two: the
definitions at agda/X.agda, the lemmas at agda/proof/X.agda.  For the
counts below the two halves are one unit (as they were one module before
the split): they belong to the same group, and a proof reaches the unit
when it reaches either half.  So the totals do not depend on the split,
except for the module lines and re-exports of the proof halves.

Language-independent infrastructure (side 'infra') is reported in a
separate table and is not in any total.  The test is whether the code
would be used, unchanged, by other languages and compilers: abstract
binding trees and lemmas about the syntax of any signature, list lookups,
base types, the denotational framework (sets as predicates, environments,
the semantics of any signature, DOp signatures), the graph model (values,
consistency, operators and their continuity: the semantic algebra), the
small-step framework (transition systems, forward simulations, runs from
any state) and the clocked one, both over any type of observations.  The meaning of this
compiler's primitives (Semantics/Graph/Prim.agda, as the machines'
and interpreters' prim?) and its observations
(Semantics/Observation.agda) are not
infrastructure.  The operational values are not either: each language's
Val is its own datatype (closures over that language's terms, code
pointers into its tables), observed through this compiler's
observations.  For each infrastructure group, the separate table shows
the lines of its modules that each proof reaches.  The script fails if an
infrastructure module imports a module that is not infrastructure.

The graph model's infrastructure is three groups, so that each semantic
algebra is charged only for the operators it uses: what any graph-model
semantics uses (values, consistency, the machinery for any operators,
and the operators both models share unchanged), the graph model's
operators, and the error-propagating operators of the graph model with
errors.  The graph model with errors (side 'gerr', its adequacy
'gadeq') is a fifth column, printed next to the four but not in their
comparison (shared modules reached by all four are still the ones not
counted): it is counted as they are, plus the graph model's meaning of
the primitives, which it extends; its adequacy as adequacy is.  The
script checks that it reaches no module of the other proofs but that
one, and that it and its adequacy reach none of the graph model's
operator modules, and prints the infrastructure each graph model
reaches.

A group may belong to two proofs ('op+red': the machines of Imp, CFG and
X86 and the proofs of explicate control and select instructions, shared by
the CEK and reduction proofs); it is counted in full in that row of both.

Totals come from the import graph (`import`/`open import` lines, with or
without `as`, `using`, module arguments or `public`).  A proof's total is
its own modules plus the shared modules it reaches transitively that are
not reached by all four proofs; shared modules reached by all four are
not counted anywhere, and infrastructure is never counted.  Adequacy, an
add-on to the denotational proof, also counts the shared modules it
reaches that the denotational total does not already count.  The script
also fails if one proof reaches another proof's modules, adequacy's or an
experiment's.

The public theorem statements (agda/Theorems/) are new boilerplate (each
restates a theorem of the proofs with its type), so they are not in the
totals; they are in the audit-surface table, which gives, for each style,
the lines of the audit surface that its statements reach: the shared
part (languages, passes, syntax), counted once, the semantics of that
style, and the statements.  The script fails if a module of the audit
surface imports a module of agda/proof/ (the theorem files do, by
design), or if a module outside agda/proof/ is not reached from the
theorem files.
"""
import glob, os, re, sys

L = 'agda/Language/'
C = 'agda/Compiler/'
G = 'agda/Semantics/Graph/'
O = 'agda/Semantics/CEK/'
F = 'agda/Semantics/Interp/'
RD = 'agda/Semantics/Reduction/'
PC = 'agda/proof/Compiler/'
GP = 'agda/proof/Semantics/Graph/'
OP = 'agda/proof/Semantics/CEK/'
FP = 'agda/proof/Semantics/Interp/'
RP = 'agda/proof/Semantics/Reduction/'
GC = 'agda/proof/Correctness/Graph/'
OC = 'agda/proof/Correctness/CEK/'
FC = 'agda/proof/Correctness/Interp/'
RC = 'agda/proof/Correctness/Reduction/'
AP = 'agda/proof/Adequacy/'
W = 'agda/Framework/'
WP = 'agda/proof/Framework/'
GE = 'agda/Semantics/GraphErr/'
GEP = 'agda/proof/Semantics/GraphErr/'
GEC = 'agda/proof/Correctness/GraphErr/'
GEA = 'agda/proof/Adequacy/GraphErr/'

# (side, group, glob patterns)
GROUPS = [
    # also the lemmas the operational styles use about the compiler's
    # output, Compiler/{EncloseScope,GlobalizeTable,PipelineScope}, and the
    # observations (Observation.agda).  Those not used by all four proofs
    # are counted in each proof that uses them (see main).
    ('shared', 'syntax, languages, compiler passes',
     [L + '*.agda', C + '*.agda', PC + '*.agda', 'agda/Semantics/Observation.agda']),

    # language-independent infrastructure: not in the totals (see main)
    ('infra', 'abstract binding trees',
     [W + 'abt/AbstractBindingTree.agda', W + 'abt/GSubst.agda', W + 'abt/ScopedTuple.agda',
      WP + 'abt/ScopedTuple.agda', W + 'abt/Sig.agda', W + 'abt/Var.agda',
      W + 'Syntax/SigUtil.agda', W + 'Syntax/SyntaxUtil.agda']),
    ('infra', 'syntax lemmas (renaming, scoping, uses), list lookups',
     [W + 'Syntax/Uses.agda', W + 'Syntax/Scope.agda', W + 'Syntax/Rename.agda', W + 'Syntax/Subst.agda',
      WP + 'Syntax/*.agda', W + 'ListUtil.agda', WP + 'ListUtil.agda']),
    ('infra', 'base types, logical equivalence', [W + 'Primitives.agda', W + 'Iff.agda']),
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
    # graph model; and the error-propagating operators of the graph model
    # with errors (the pilot, see loc.md)
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
    ('infra', 'small-step framework: transition systems, simulations',
     [W + 'Smallstep.agda', WP + 'Smallstep.agda', WP + 'Simulation.agda']),
    ('infra', 'reduction framework: reduction semantics, simulations between them',
     [W + 'Reduction.agda', WP + 'Reduction.agda']),
    ('infra', 'clocked big-step framework', [W + 'Clocked.agda', WP + 'Clocked.agda']),
    # runs of a step function from any state, for the logical relations of
    # adequacy
    ('infra', 'runs of a step function from any state', [WP + 'Runs.agda']),

    # the meaning of the primitives (Prim.agda) is here, as prim? is in
    # each machine and interpreter
    ('den', 'semantics of the languages',
     [G + 'Prim.agda', GP + 'Prim.agda',
      G + 'ISWIM.agda', GP + 'ISWIM.agda', GP + 'ISWIMContinuous.agda',
      G + 'Clos2Iswim.agda', GP + 'Clos2Iswim.agda',
      G + 'Clos3Iswim.agda', GP + 'Clos3Iswim.agda',
      G + 'Clos4Iswim.agda', GP + 'Clos4Iswim.agda',
      G + 'Clos5Iswim.agda', GP + 'Clos5IswimContinuous.agda',
      G + 'Imp.agda', G + 'ImpK.agda', G + 'CFG.agda', G + 'X86.agda']),
    # simplify's syntactic lemmas (SimplifyFacts) are used by all four of its
    # proofs, so they are counted in the simplify row of each column
    ('den+op+ck+red+gerr', 'simplify', [PC + 'SimplifyFacts.agda']),
    ('den', 'simplify', [GC + 'SimplifyCorrect.agda']),
    ('den', 'CC: enclose', [GC + 'EncloseCorrect.agda']),
    ('den', 'CC: optimize', [GC + 'OptimizeCorrect.agda']),
    ('den', 'CC: concretize', [GC + 'ConcretizeCorrect.agda']),
    ('den', 'CC: delay',
     [GC + 'DelayFiniteCommon.agda', GC + 'DelayFiniteRel.agda',
      GC + 'DelayApp.agda', GC + 'DelayPreserve.agda',
      GC + 'DelayReflectFinite.agda']),
    ('den', 'CC: globalize', [GC + 'GlobalizeCorrect.agda']),
    # each rco module also proves compile-mon (compile then rco) end to end
    ('den', 'rco', [GC + 'RCOCorrect.agda']),
    # lift locals and explicate control against the continuation-passing
    # semantics of Imp (Semantics/Graph/ImpK.agda); against the direct one,
    # see 'exp'
    ('den', 'lift locals',
     [GC + 'LiftLocalsCommon.agda', GC + 'LiftLocalsCorrectK.agda']),
    ('den', 'explicate control',
     [GC + 'ExplicateCommon.agda', GC + 'ExplicateCorrectK.agda']),
    ('den', 'select instructions', [GC + 'SelectCorrect.agda']),
    ('den', 'composition', [GC + 'CompilerCorrect.agda']),

    # with the framework at this compiler's observations (Smallstep.agda,
    # Simulation.agda).  The machines of the first-order languages Imp, CFG
    # and X86, and the framework instances, are shared with the reduction
    # proof ('op+red': counted in both columns)
    ('op', 'semantics of the languages',
     [O + 'ISWIM.agda', O + 'Clos2.agda', O + 'Clos3.agda',
      O + 'Clos4.agda', O + 'Clos5.agda']),
    ('op+red', 'semantics of the languages',
     [O + 'Values.agda', O + 'Imp.agda', O + 'CFG.agda', O + 'X86.agda',
      O + 'Smallstep.agda', OP + 'Smallstep.agda', OP + 'Simulation.agda']),
    ('op', 'simplify', [OC + 'SimplifySim.agda']),
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
    ('op', 'composition', [OC + 'CompilerSim.agda', OC + 'CompilerX86Sim.agda']),

    # reduction semantics (substitution) for the languages with binders,
    # and the framework at this compiler's observations (Smallstep.agda)
    ('red', 'semantics of the languages', [RD + '*.agda', RP + '*.agda']),
    ('red', 'simplify', [RC + 'SimplifyRed.agda']),
    ('red', 'CC: enclose', [RC + 'EncloseRed.agda']),
    ('red', 'CC: optimize', [RC + 'OptimizeRed.agda']),
    ('red', 'CC: concretize', [RC + 'ConcretizeRed.agda']),
    ('red', 'CC: delay', [RC + 'DelayRed.agda']),
    ('red', 'CC: globalize', [RC + 'GlobalizeRed.agda']),
    ('red', 'rco', [RC + 'RCORed.agda']),
    ('red', 'lift locals', [RC + 'LiftLocalsRed.agda']),
    ('red', 'composition', [RC + 'CompilerRed.agda', RC + 'CompilerX86Red.agda']),

    # with the framework at this compiler's observations (Clock.agda)
    ('ck', 'semantics of the languages', [F + '*.agda', FP + 'Clock.agda']),
    ('ck', 'simplify', [FC + 'SimplifyFuel.agda']),
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

    ('adeq', 'ISWIM',
     [AP + 'Common.agda', AP + 'Soundness.agda', AP + 'LogRel.agda',
      AP + 'ISWIM.agda']),
    ('adeq', 'Clos5',
     [AP + 'Clos5Common.agda', AP + 'Clos5Soundness.agda', AP + 'Clos5LogRel.agda',
      AP + 'Clos5.agda', AP + 'Values.agda']),
    ('adeq', 'X86',
     [AP + 'X86Common.agda', AP + 'X86Soundness.agda', AP + 'X86LogRel.agda',
      AP + 'X86.agda']),
    ('adeq', 'well-formedness of compiled programs',
     [AP + 'Clos5WF.agda', AP + 'CompileWF.agda', AP + 'X86WF.agda',
      AP + 'X86CompileWF.agda']),
    ('adeq', 'end to end', [AP + 'EndToEnd.agda']),

    ('examples', 'examples',
     [GC + '*Example.agda', PC + 'Examples/*.agda']),

    # not in the totals: a direct backward simulation for delay, without
    # determinism, for comparison (see loc.md)
    ('exp', 'simulation: direct backward simulation for delay — framework',
     [OP + 'Backward.agda']),
    ('exp', 'simulation: direct backward simulation for delay — delay',
     [OC + 'DelayBackSim.agda']),
    # not in the totals: the direct semantics of Imp (ImpDirect.agda),
    # an alternative to the continuation-passing one, and lift locals and
    # explicate control proved against it.  They also use
    # Semantics/Graph/Imp.agda, LiftLocalsCommon and ExplicateCommon, counted in the main rows.
    ('exp', 'graph model: direct Imp — semantics', [GP + 'ImpDirect.agda']),
    ('exp', 'graph model: direct Imp — lift locals', [GC + 'LiftLocalsCorrect.agda']),
    ('exp', 'graph model: direct Imp — explicate control',
     [GC + 'ExplicateCorrect.agda']),

    # the graph model with errors (ω): a fifth column, not (yet) in the
    # comparison of the four (see loc.md), and its adequacy
    ('gerr', 'semantics of the languages',
     [GE + '*.agda', GEP + '*.agda']),
    ('gerr', 'simplify', [GEC + 'SimplifyCorrect.agda']),
    ('gerr', 'CC: enclose', [GEC + 'EncloseCorrect.agda']),
    ('gerr', 'CC: optimize', [GEC + 'OptimizeCorrect.agda']),
    ('gerr', 'CC: concretize', [GEC + 'ConcretizeCorrect.agda']),
    ('gerr', 'CC: delay',
     [GEC + 'DelayRel.agda', GEC + 'DelayApp.agda', GEC + 'DelayReflect.agda', GEC + 'DelayPreserve.agda']),
    ('gerr', 'CC: globalize', [GEC + 'GlobalizeCorrect.agda']),
    ('gerr', 'rco', [GEC + 'RCOCorrect.agda']),
    ('gerr', 'lift locals', [GEC + 'LiftLocalsCorrect.agda']),
    ('gerr', 'explicate control', [GEC + 'ExplicateCorrect.agda']),
    ('gerr', 'select instructions', [GEC + 'SelectCorrect.agda']),
    ('gerr', 'composition', [GEC + 'CompilerCorrect.agda']),
    ('gadeq', 'ISWIM', [GEA + 'Soundness.agda', GEA + 'LogRel.agda', GEA + 'ISWIM.agda']),
    ('gadeq', 'Clos5',
     [GEA + 'Clos5Common.agda', GEA + 'Clos5Soundness.agda', GEA + 'Clos5LogRel.agda', GEA + 'Clos5.agda']),
    ('gadeq', 'X86',
     [GEA + 'X86Common.agda', GEA + 'X86Consistent.agda', GEA + 'X86Soundness.agda',
      GEA + 'X86LogRel.agda', GEA + 'X86.agda']),
    ('gadeq', 'well-formedness of compiled programs', [GEA + 'Clos5WF.agda', GEA + 'X86WF.agda']),
    ('gadeq', 'end to end', [GEA + 'EndToEnd.agda']),
    ('gadeq', 'simplify through the ISWIM machine', [GEA + 'Simplify.agda']),

    # not in the totals: the public theorem statements (see the audit-surface
    # table)
    ('thm', 'theorem statements', ['agda/Theorems/*.agda']),
]

THEOREMS = {'den': 'agda/Theorems/Denotational.agda', 'op': 'agda/Theorems/Simulation.agda',
            'ck': 'agda/Theorems/Interpreter.agda', 'red': 'agda/Theorems/Reduction.agda',
            'adeq': 'agda/Theorems/Adequacy.agda', 'gerr': 'agda/Theorems/GraphErrors.agda'}


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


def code_lines(path):
    """The code lines of path, not counting import statements: a line that
    starts with `import` or `open import`, and the lines after it that are
    indented more deeply (its continuation)."""
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
    return n


# `import M`, `open import M`, `import M as X`, `open import M args using (…)`,
# `… public`, with the module name possibly on the next line.
IMPORT = re.compile(r'(?<![^\s;{(])(?:open\s+)?import\s+([^\s;(){}]+)')


def imports(path):
    """Files under agda/ that path imports (library modules are ignored)."""
    text = strip_comments(open(path, encoding='utf-8').read())
    out = set()
    for m in IMPORT.finditer(text):
        f = 'agda/' + m.group(1).replace('.', '/') + '.agda'
        if os.path.exists(f):
            out.add(f)
    return out


def unit(f):
    """The unit of a file: agda/X.agda for both agda/X.agda and its proof half
    agda/proof/X.agda."""
    return 'agda/' + f[len('agda/proof/'):] if f.startswith('agda/proof/') else f


def reachable(roots, graph):
    seen, todo = set(), list(roots)
    while todo:
        f = todo.pop()
        if f not in seen:
            seen.add(f)
            todo.extend(graph[f])
    return seen


def modname(u):
    return u[len("agda/"):-len(".agda")].replace("/", ".")


SIDES = ('den', 'op', 'ck', 'red')
# column labels, and the short names used in lists and messages
LABELS = {'den': 'denotational: graph model', 'op': 'CEK machine + simulation',
          'ck': 'clocked interpreter + value relations',
          'red': 'reduction semantics + simulation', 'adeq': 'adequacy',
          'gerr': 'graph model with errors', 'gadeq': 'adequacy with errors'}
NAMES = {'den': 'graph model', 'op': 'simulation', 'ck': 'interpreter',
         'red': 'reduction', 'adeq': 'adequacy', 'gerr': 'graph model with errors',
         'gadeq': 'adequacy with errors'}
EXTRA = 'shared modules not used by all four proofs'


def sides_of(side):
    """The proofs a group belongs to: 'op+red' is counted in both."""
    return side.split('+')


def bold_min(ns):
    """Cells for the numbers ns (None for a missing entry), with the lowest
    in bold when at least two entries are present: the best result."""
    present = [n for n in ns if n is not None]
    low = min(present) if len(present) >= 2 else None
    return [('—' if n is None else f'**{n}**' if n == low else str(n)) for n in ns]


def main():
    seen, counts, files_of = {}, {}, {}
    # a file named explicitly by a group is not matched by another's wildcard
    explicit = {p for _, _, pats in GROUPS for p in pats if '*' not in p}
    for side, name, pats in GROUPS:
        files = sorted({f for p in pats for f in glob.glob(p)
                        if '*' not in p or f not in explicit})
        if not files:
            if side in ('ck', 'red', 'gerr', 'gadeq'):
                continue
            sys.exit(f'no files for group {side}/{name}')
        for f in files:
            if f in seen:
                sys.exit(f'{f} is in two groups')
            seen[f] = (side, name)
        files_of[(side, name)] = files
        for s in sides_of(side):
            counts[(s, name)] = counts.get((s, name), 0) + sum(code_lines(f) for f in files)
    every = {f for f in glob.glob('agda/**/*.agda', recursive=True)
             if not f.startswith('agda/old/') and f != 'agda/All.agda'}
    missing = sorted(every - set(seen))
    if missing:
        sys.exit('not in any group:\n  ' + '\n  '.join(missing))

    # units: the two halves of a split module count as one module
    files_of_unit = {}
    for f in every:
        files_of_unit.setdefault(unit(f), []).append(f)
    group_of = {}
    for u, fs in files_of_unit.items():
        gs = {seen[f] for f in fs}
        if len(gs) > 1:
            sys.exit(f'the halves of {u} are in different groups: {sorted(gs)}')
        group_of[u] = gs.pop()
    units = set(files_of_unit)

    def ulines(u):
        return sum(code_lines(f) for f in files_of_unit[u])

    graph = {u: {unit(g) for f in files_of_unit[u] for g in imports(f)} - {u} for u in units}
    own = {s: {u for u, (side, _) in group_of.items() if s in sides_of(side)}
           for s in SIDES + ('adeq', 'gerr', 'gadeq')}
    exp = {u for u, (side, _) in group_of.items() if side in ('exp', 'gerr', 'gadeq')}
    infra = {u for u, (side, _) in group_of.items() if side == 'infra'}
    reach = {s: reachable(own[s], graph) for s in own}

    # Infrastructure is language independent: it imports only infrastructure.
    bad = sorted(u for u in reachable(infra, graph) - infra)
    if bad:
        sys.exit('infrastructure imports modules that are not infrastructure:\n  '
                 + '\n  '.join(bad))

    # The proofs must be independent: no proof reaches another proof's modules
    # nor adequacy's, nor an experiment or the pilot (adequacy, examples, the
    # experiments and the pilot may use anything).
    for s in SIDES:
        for t in SIDES + ('adeq',):
            bad = sorted(reach[s] & (own[t] - own[s])) if s != t else []
            if bad:
                sys.exit(f'{NAMES[s]} imports {NAMES[t]} modules:\n  ' + '\n  '.join(bad))
        bad = sorted(reach[s] & exp)
        if bad:
            sys.exit(f'{NAMES[s]} imports experiment modules:\n  ' + '\n  '.join(bad))
    # The graph model with errors reaches no module of the other proofs, but
    # the graph model's meaning of the primitives, which primᵉ extends.
    for t in ('op', 'ck', 'red', 'adeq', 'gadeq'):
        bad = sorted(reach['gerr'] & (own[t] - own['gerr']))
        if bad:
            sys.exit(f'graph model with errors imports {NAMES[t]} modules:\n  ' + '\n  '.join(bad))
    bad = sorted(reach['gerr'] & (own['den'] - own['gerr']) - {G + 'Prim.agda'})
    if bad:
        sys.exit('graph model with errors imports graph model modules:\n  ' + '\n  '.join(bad))

    # The audit surface: every module outside agda/proof/, reached from the
    # theorem files through modules outside agda/proof/, and importing none
    # of agda/proof/ (but the theorem files, which cite the proofs).
    fgraph = {f: imports(f) for f in every}
    thm = set(THEOREMS.values())
    if thm != {f for f, (side, _) in seen.items() if side == 'thm'}:
        sys.exit('the theorem files are not ' + ', '.join(sorted(thm)))
    surface = {f for f in every if not f.startswith('agda/proof/')}
    sgraph = {f: {g for g in fgraph[f] if g in surface} for f in surface}
    for f in sorted(surface - thm):
        bad = sorted(g for g in fgraph[f] if g.startswith('agda/proof/'))
        if bad:
            sys.exit(f'{f}, on the audit surface, imports proof modules:\n  ' + '\n  '.join(bad))
    unreached = sorted(surface - reachable(thm, sgraph))
    if unreached:
        sys.exit('outside agda/proof/ but not reached from the theorem files:\n  '
                 + '\n  '.join(unreached))

    shared = {u for u, (side, _) in group_of.items() if side == 'shared'}
    by_all = shared & reach['den'] & reach['op'] & reach['ck'] & reach['red']
    extra = {s: sorted((shared & reach[s]) - by_all) for s in SIDES}
    # Adequacy is an add-on to the denotational proof, so shared modules that
    # the denotational proof already counts are not counted again.
    extra['adeq'] = sorted((shared & reach['adeq']) - by_all - set(extra['den']))
    unused = sorted(shared - set().union(*(reach[s] for s in own)))
    # The graph model with errors is counted as the four are: its own
    # modules and the shared ones it reaches that all four do not; and the
    # graph model's modules it uses (the meaning of the primitives).  Its
    # adequacy is counted as adequacy is: what it adds to its proof.
    extra['gerr'] = sorted((shared & reach['gerr']) - by_all)
    borrowed = {'gerr': sorted(reach['gerr'] & (own['den'] - own['gerr']))}
    extra['gadeq'] = sorted((shared & reach['gadeq']) - by_all - set(extra['gerr']))
    borrowed['gadeq'] = sorted(reach['gadeq'] & ((own['den'] | own['adeq']) - own['gerr'])
                               - reach['gerr'])

    rows = ['semantics of the languages', 'simplify', 'CC: enclose', 'CC: optimize', 'CC: concretize',
            'CC: delay', 'CC: globalize', 'rco', 'lift locals', 'explicate control',
            'select instructions',
            'composition']
    MCOLS = SIDES + ('gerr',)
    total = {side: 0 for side in MCOLS}
    print('| component | ' + ' | '.join(LABELS[s] for s in MCOLS) + ' |')
    print('|---|' + '---:|' * len(MCOLS))
    for r in rows:
        ns = []
        for side in MCOLS:
            n = counts.get((side, r))
            total[side] += n or 0
            ns.append(n)
        print(f'| {r} | ' + ' | '.join(bold_min(ns)) + ' |')
    ns = []
    for side in MCOLS:
        n = sum(ulines(u) for u in extra[side])
        total[side] += n
        ns.append(n if extra[side] else None)
    print(f'| {EXTRA} | ' + ' | '.join(bold_min(ns)) + ' |')
    n = sum(ulines(u) for u in borrowed['gerr'])
    total['gerr'] += n
    print("| the graph model's meaning of the primitives | — | — | — | — | " + str(n) + ' |')
    print('| **total** | ' + ' | '.join(bold_min([total[side] for side in MCOLS])) + ' |')
    print()

    def lines(us):
        return sum(ulines(u) for u in us)
    ICOLS = SIDES + ('gerr',)
    print('| language-independent infrastructure (not in the totals) | lines | '
          + ' | '.join(f'used by {LABELS[s]}' for s in ICOLS) + ' |')
    print('|---|---:|' + '---:|' * len(ICOLS))
    itotal = {s: 0 for s in ICOLS}
    for side, name, _ in GROUPS:
        if side == 'infra':
            us = {unit(f) for f in files_of[(side, name)]}
            cells = []
            for s in ICOLS:
                n = lines(u for u in us if u in reach[s])
                itotal[s] += n
                cells.append(str(n) if n else '—')
            print(f'| {name} | {counts[(side, name)]} | ' + ' | '.join(cells) + ' |')
    print(f'| **total** | {lines(infra)} | '
          + ' | '.join(str(itotal[s]) for s in ICOLS) + ' |')
    print()
    print(f"Adequacy uses {lines(infra & reach['adeq'])} lines of the infrastructure, "
          f"{lines(infra & reach['adeq'] - reach['den'])} of them not used by the denotational proof.")
    print()
    print('| adequacy (denotational side only) | graph model | graph model with errors |')
    print('|---|---:|---:|')
    adeq = {'adeq': 0, 'gadeq': 0}
    anames = []
    for side, name, _ in GROUPS:
        if side in ('adeq', 'gadeq') and name not in anames:
            anames.append(name)
    for name in anames:
        ns = []
        for s in ('adeq', 'gadeq'):
            n = counts.get((s, name))
            adeq[s] += n or 0
            ns.append(n)
        print(f'| {name} | ' + ' | '.join(bold_min(ns)) + ' |')
    ns = []
    for s in ('adeq', 'gadeq'):
        n = sum(ulines(u) for u in extra[s])
        adeq[s] += n
        ns.append(n if extra[s] else None)
    print(f'| {EXTRA}, nor by the proof of its model | ' + ' | '.join(bold_min(ns)) + ' |')
    n = sum(ulines(u) for u in borrowed['gadeq'])
    adeq['gadeq'] += n
    print(f"| the graph model's adequacy modules it uses | — | {n if borrowed['gadeq'] else '—'} |")
    print('| **total** | ' + ' | '.join(bold_min([adeq['adeq'], adeq['gadeq']])) + ' |')
    print()
    print('| experiment (not in the totals) | lines |')
    print('|---|---:|')
    for side, name, _ in GROUPS:
        if side == 'exp':
            print(f'| {name} | {counts[(side, name)]} |')
    print()

    # The audit surface of each style: the modules outside agda/proof/ that
    # its theorem file reaches, by kind.
    def kind(f):
        side, name = seen[f]
        if side == 'thm':
            return 'statements'
        if side == 'shared' or (side == 'infra' and name in (
                'abstract binding trees', 'syntax lemmas (renaming, scoping, uses), list lookups',
                'base types, logical equivalence')):
            return 'shared'
        return 'semantics'
    sreach = {s: reachable({THEOREMS[s]}, sgraph) for s in THEOREMS}
    ALL = ('den', 'op', 'ck', 'red', 'adeq', 'gerr')
    def flines(fs):
        return sum(code_lines(f) for f in fs)
    sh = {s: {f for f in sreach[s] if kind(f) == 'shared'} for s in ALL}
    shared_all = set().union(*sh.values())
    print('| audit surface (not in the totals) | lines | '
          + ' | '.join(f'read for {LABELS[s]}' for s in ALL) + ' |')
    print('|---|---:|' + '---:|' * len(ALL))
    print(f'| languages, compiler passes, syntax, base types (shared) | {flines(shared_all)} | '
          + ' | '.join(str(flines(sh[s])) for s in ALL) + ' |')
    SEMS = {'den': 'domain, operators, semantics of each language',
            'op': 'small-step machines, transition systems',
            'ck': 'clocked interpreters, results',
            'red': 'reduction semantics, machines of Imp, CFG and X86, transition systems',
            'gerr': 'domain, error-propagating operators, semantics of each language'}
    sem_files = {s: {f for f in sreach[s] if kind(f) == 'semantics'} for s in ALL}
    for s in SIDES + ('gerr',):
        fs = sem_files[s]
        print(f'| {NAMES[s]}: {SEMS[s]} | {flines(fs)} | '
              + ' | '.join(str(flines(sem_files[t] & fs)) if sem_files[t] & fs else '—' for t in ALL) + ' |')
    for s in ALL:
        print(f'| {NAMES[s]}: theorem statements | {code_lines(THEOREMS[s])} | '
              + ' | '.join(str(code_lines(THEOREMS[s])) if t == s else '—' for t in ALL) + ' |')
    tot = {s: flines(sreach[s] - (thm - {THEOREMS[s]})) for s in ALL}
    alls = surface
    styles = [s for s in ALL if s != 'adeq']
    low = min(tot[s] for s in styles)
    print(f'| **total** | {flines(alls)} | '
          + ' | '.join(f'**{tot[s]}**' if s != 'adeq' and tot[s] == low else str(tot[s]) for s in ALL) + ' |')
    print()
    print(f'The adequacy statements also use ρ₀ from the denotational ones '
          f'(Theorems/Denotational.agda), not counted in its column.')
    print()

    def mods(us):
        return ', '.join(f'`{modname(u)}` ({ulines(u)})' for u in us) or 'none'

    def split_mark(u):
        return ' (+ proof/)' if len(files_of_unit[u]) > 1 or not os.path.exists(u) else ''
    print('| shared module | lines | used by |')
    print('|---|---:|---|')
    for u in sorted(shared):
        users = [NAMES[s] for s in SIDES + ('adeq', 'gerr', 'gadeq') if u in reach[s]]
        tag = 'all four proofs' if u in by_all else (', '.join(users) or 'no proof')
        name = ('proof.' if not os.path.exists(u) else '') + modname(u)
        print(f'| `{name}`{split_mark(u) if os.path.exists(u) else ""} | {ulines(u)} | {tag} |')
    print()
    nall = sum(ulines(u) for u in by_all)
    print('| infrastructure module | lines | used by |')
    print('|---|---:|---|')
    for u in sorted(infra):
        users = [NAMES[s] for s in SIDES + ('adeq', 'gerr', 'gadeq') if u in reach[s]]
        name = ('proof.' if not os.path.exists(u) else '') + modname(u)
        print(f'| `{name}`{split_mark(u) if os.path.exists(u) else ""} | {ulines(u)} | '
              f'{", ".join(users) or "no proof"} |')
    print()
    print(f'Shared by all four proofs, not counted: {len(by_all)} modules, {nall} lines.')
    for s in SIDES + ('adeq', 'gerr', 'gadeq'):
        print(f'Counted in {NAMES[s]}: {mods(extra[s])}.')
    for s in ('gerr', 'gadeq'):
        print(f'Of the graph model, counted in {NAMES[s]}: {mods(borrowed[s])}.')
    if unused:
        print(f'Shared but used by no proof: {mods(unused)}.')
    print(f"Examples, not counted: {counts[('examples', 'examples')]} lines.")
    print()
    errors_infra(files_of, reach, ulines)
    print()
    print(f"Module (+ proof/): the definitions are on the audit surface, the lemmas "
          f"in its proof/ half; the lines are those of both.")


def errors_infra(files_of, reach, ulines):
    """The infrastructure each graph model reaches, by group, and what they
    share: the semantics and the correctness proofs (without adequacy), and
    then what adequacy adds, in each model."""
    rd = reach['adeq'] - reach['den']
    ra = reach['gadeq'] - reach['gerr']
    print('| infrastructure group | lines | graph model | graph model with errors | both '
          '| adequacy adds: graph model | adequacy adds: graph model with errors |')
    print('|---|---:|---:|---:|---:|---:|---:|')
    tot = [0] * 6
    for side, name, _ in GROUPS:
        if side == 'infra':
            us = {unit(f) for f in files_of[(side, name)]}
            row = [sum(ulines(u) for u in us),
                   sum(ulines(u) for u in us if u in reach['den']),
                   sum(ulines(u) for u in us if u in reach['gerr']),
                   sum(ulines(u) for u in us if u in reach['den'] and u in reach['gerr']),
                   sum(ulines(u) for u in us if u in rd),
                   sum(ulines(u) for u in us if u in ra)]
            if any(row[1:]):
                tot = [t + r for t, r in zip(tot, row)]
                print(f'| {name} | {row[0]} | ' + ' | '.join(str(r) if r else '—' for r in row[1:]) + ' |')
    print('| **total** | ' + ' | '.join(str(t) for t in tot) + ' |')
    # the graph model with errors builds its operators on the graph model's
    # (its kernels): the modules of that group it reuses
    ops = {unit(f) for f in files_of[('infra', 'graph model: its operators')]}
    used = sorted(ops & (reach['gerr'] | reach['gadeq']))
    print()
    print('The graph model with errors reuses these modules of the graph model\'s operators: '
          + ', '.join(f'`{modname(u)}` ({ulines(u)})' for u in used) + '.')


if __name__ == '__main__':
    main()
