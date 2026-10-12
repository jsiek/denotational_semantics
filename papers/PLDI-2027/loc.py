#!/usr/bin/env python3
"""Count code lines of the three compiler-correctness proofs, and of the
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
small-step framework (transition systems, forward simulations) and the
clocked one, both over any type of observations.  The meaning of this
compiler's primitives (Compiler/Model/Graph/Prim.agda, as the machines'
and interpreters' prim?) and its observations (Observation.agda) are not
infrastructure.  The operational values are not either: each language's
Val is its own datatype (closures over that language's terms, code
pointers into its tables), observed through this compiler's
observations.  For each infrastructure group, the separate table shows
the lines of its modules that each proof reaches.  The script fails if an
infrastructure module imports a module that is not infrastructure.

Totals come from the import graph (`import`/`open import` lines, with or
without `as`, `using`, module arguments or `public`).  A proof's total is
its own modules plus the shared modules it reaches transitively that are
not reached by all three proofs; shared modules reached by all three are
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

L = 'agda/Compiler/Lang/'
C = 'agda/Compiler/Compile/'
G = 'agda/Compiler/Model/Graph/'
O = 'agda/Compiler/Operational/'
F = 'agda/Compiler/Functional/'
RD = 'agda/Compiler/Reduction/'
PC = 'agda/proof/Compiler/'
GP = PC + 'Model/Graph/'
OP = PC + 'Operational/'
FP = PC + 'Functional/'
RP = PC + 'Reduction/'
W = 'agda/Framework/'
WP = 'agda/proof/Framework/'

# (side, group, glob patterns)
GROUPS = [
    # also the lemmas both operational styles use about the compiler's
    # output, Compile/{EncloseScope,GlobalizeTable,PipelineScope}, and the
    # observations (Observation.agda).  Those not used by all three proofs
    # are counted in each proof that uses them (see main).
    ('shared', 'syntax, languages, compiler passes',
     [L + '*.agda', C + '*.agda', PC + 'Compile/*.agda', 'agda/Compiler/Observation.agda']),

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
      W + 'abt/Fold2.agda', WP + 'GraphModel/RenameSem.agda']),
    ('infra', 'graph model: values, operators, continuity',
     [W + 'GraphModel/Domain.agda', WP + 'GraphModel/Domain.agda',
      W + 'GraphModel/Ops.agda', WP + 'GraphModel/Ops.agda',
      WP + 'GraphModel/Continuity.agda', WP + 'GraphModel/SemanticsUtil.agda']),
    ('infra', 'small-step framework: transition systems, simulations',
     [W + 'Smallstep.agda', WP + 'Smallstep.agda', WP + 'Simulation.agda']),
    ('infra', 'reduction framework: reduction semantics, simulations between them',
     [W + 'Reduction.agda', WP + 'Reduction.agda']),
    ('infra', 'clocked big-step framework', [W + 'Clocked.agda', WP + 'Clocked.agda']),

    # the meaning of the primitives (Prim.agda) is here, as prim? is in
    # each machine and interpreter
    ('den', 'semantics of the languages',
     [G + 'Prim.agda', GP + 'Prim.agda',
      G + 'Sem/ISWIM.agda', GP + 'Sem/ISWIM.agda',
      G + 'Sem/Clos2Iswim.agda', GP + 'Sem/Clos2Iswim.agda',
      G + 'Sem/Clos3Iswim.agda', GP + 'Sem/Clos3Iswim.agda', GP + 'Sem/Clos3IswimContinuous.agda',
      G + 'Sem/Clos4Iswim.agda', GP + 'Sem/Clos4Iswim.agda', GP + 'Sem/Clos4IswimContinuous.agda',
      G + 'Sem/Clos5Iswim.agda', GP + 'Sem/Clos5IswimContinuous.agda',
      G + 'Sem/Imp.agda', G + 'Sem/ImpK.agda', G + 'Sem/CFG.agda', G + 'Sem/X86.agda']),
    ('den', 'enclose', [GP + 'Correctness/EncloseCorrect.agda']),
    ('den', 'optimize', [GP + 'Correctness/OptimizeCorrect.agda']),
    ('den', 'concretize', [GP + 'Correctness/ConcretizeCorrect.agda']),
    ('den', 'delay',
     [GP + 'Correctness/DelayFiniteCommon.agda', GP + 'Correctness/DelayFiniteRel.agda',
      GP + 'Correctness/DelayApp.agda', GP + 'Correctness/DelayPreserve.agda',
      GP + 'Correctness/DelayReflectFinite.agda']),
    ('den', 'globalize', [GP + 'Correctness/GlobalizeCorrect.agda']),
    # each rco module also proves compile-mon (compile then rco) end to end
    ('den', 'rco', [GP + 'Correctness/RCOCorrect.agda']),
    # lift locals and explicate control against the continuation-passing
    # semantics of Imp (Sem/ImpK.agda); against the direct one, see 'exp'
    ('den', 'lift locals',
     [GP + 'Correctness/LiftLocalsCommon.agda', GP + 'Correctness/LiftLocalsCorrectK.agda']),
    ('den', 'explicate control',
     [GP + 'Correctness/ExplicateCommon.agda', GP + 'Correctness/ExplicateCorrectK.agda']),
    ('den', 'select instructions', [GP + 'Correctness/SelectCorrect.agda']),
    ('den', 'composition', [GP + 'Correctness/CompilerCorrect.agda']),

    # with the framework at this compiler's observations (Smallstep.agda,
    # Simulation.agda).  The machines of the first-order languages Imp, CFG
    # and X86, and the framework instances, are shared with the reduction
    # proof ('op+red': counted in both columns)
    ('op', 'semantics of the languages',
     [O + 'Machine/ISWIM.agda', O + 'Machine/Clos2.agda', O + 'Machine/Clos3.agda',
      O + 'Machine/Clos4.agda', O + 'Machine/Clos5.agda']),
    ('op+red', 'semantics of the languages',
     [O + 'Machine/Values.agda', O + 'Machine/Imp.agda', O + 'Machine/CFG.agda', O + 'Machine/X86.agda',
      O + 'Smallstep.agda', OP + 'Smallstep.agda', OP + 'Simulation.agda']),
    ('op', 'enclose', [OP + 'Correctness/EncloseSim.agda']),
    ('op', 'optimize', [OP + 'Correctness/OptimizeSim.agda']),
    ('op', 'concretize', [OP + 'Correctness/ConcretizeSim.agda']),
    ('op', 'delay', [OP + 'Correctness/DelaySim.agda']),
    ('op', 'globalize', [OP + 'Correctness/GlobalizeSim.agda']),
    ('op', 'rco', [OP + 'Correctness/RCOSim.agda']),
    ('op', 'lift locals', [OP + 'Correctness/LiftLocalsSim.agda']),
    # explicate control and select instructions are between the machines of
    # first-order languages, and are shared with the reduction proof
    ('op+red', 'explicate control', [OP + 'Correctness/ExplicateSim.agda']),
    ('op+red', 'select instructions', [OP + 'Correctness/SelectSim.agda']),
    ('op', 'composition', [OP + 'Correctness/CompilerSim.agda', OP + 'Correctness/CompilerX86Sim.agda']),

    # reduction semantics (substitution) for the languages with binders,
    # and the framework at this compiler's observations (Smallstep.agda)
    ('red', 'semantics of the languages', [RD + '*.agda', RP + '*.agda']),
    ('red', 'enclose', [RP + 'Correctness/EncloseRed.agda']),
    ('red', 'optimize', [RP + 'Correctness/OptimizeRed.agda']),
    ('red', 'concretize', [RP + 'Correctness/ConcretizeRed.agda']),
    ('red', 'delay', [RP + 'Correctness/DelayRed.agda']),
    ('red', 'globalize', [RP + 'Correctness/GlobalizeRed.agda']),
    ('red', 'rco', [RP + 'Correctness/RCORed.agda']),
    ('red', 'lift locals', [RP + 'Correctness/LiftLocalsRed.agda']),
    ('red', 'composition', [RP + 'Correctness/CompilerRed.agda', RP + 'Correctness/CompilerX86Red.agda']),

    # with the framework at this compiler's observations (Clock.agda)
    ('ck', 'semantics of the languages', [F + 'Interp/*.agda', F + 'Clock.agda', FP + 'Clock.agda']),
    ('ck', 'enclose', [FP + 'Correctness/EncloseFuel.agda']),
    ('ck', 'optimize', [FP + 'Correctness/OptimizeFuel.agda']),
    ('ck', 'concretize', [FP + 'Correctness/ConcretizeFuel.agda']),
    ('ck', 'delay', [FP + 'Correctness/DelayFuel.agda']),
    ('ck', 'globalize', [FP + 'Correctness/GlobalizeFuel.agda']),
    ('ck', 'rco', [FP + 'Correctness/RCOFuel.agda']),
    ('ck', 'lift locals', [FP + 'Correctness/LiftLocalsFuel.agda']),
    ('ck', 'explicate control', [FP + 'Correctness/ExplicateFuel.agda']),
    ('ck', 'select instructions', [FP + 'Correctness/SelectFuel.agda']),
    ('ck', 'composition', [FP + 'Correctness/CompilerFuel.agda']),

    ('adeq', 'ISWIM',
     [OP + 'Adequacy/Common.agda', OP + 'Adequacy/Soundness.agda', OP + 'Adequacy/LogRel.agda',
      OP + 'Adequacy/ISWIM.agda', GP + 'Sem/ISWIMContinuous.agda']),
    ('adeq', 'Clos5',
     [OP + 'Adequacy/Clos5Common.agda', OP + 'Adequacy/Clos5Soundness.agda', OP + 'Adequacy/Clos5LogRel.agda',
      OP + 'Adequacy/Clos5.agda', OP + 'Adequacy/Values.agda']),
    ('adeq', 'X86',
     [OP + 'Adequacy/X86Common.agda', OP + 'Adequacy/X86Soundness.agda', OP + 'Adequacy/X86LogRel.agda',
      OP + 'Adequacy/X86.agda']),
    ('adeq', 'well-formedness of compiled programs',
     [OP + 'Adequacy/Clos5WF.agda', OP + 'Adequacy/CompileWF.agda', OP + 'Adequacy/X86WF.agda',
      OP + 'Adequacy/X86CompileWF.agda']),
    ('adeq', 'end to end', [OP + 'Adequacy/EndToEnd.agda']),

    ('examples', 'examples',
     [GP + 'Correctness/*Example.agda', PC + 'Compile/Examples/*.agda']),

    # not in the totals: a direct backward simulation for delay, without
    # determinism, for comparison (see loc.md)
    ('exp', 'simulation: direct backward simulation for delay — framework',
     [OP + 'Backward.agda']),
    ('exp', 'simulation: direct backward simulation for delay — delay',
     [OP + 'Correctness/DelayBackSim.agda']),
    # not in the totals: the direct semantics of Imp (Sem/ImpDirect.agda),
    # an alternative to the continuation-passing one, and lift locals and
    # explicate control proved against it.  They also use Sem/Imp.agda,
    # LiftLocalsCommon and ExplicateCommon, counted in the main rows.
    ('exp', 'graph model: direct Imp — semantics', [GP + 'Sem/ImpDirect.agda']),
    ('exp', 'graph model: direct Imp — lift locals', [GP + 'Correctness/LiftLocalsCorrect.agda']),
    ('exp', 'graph model: direct Imp — explicate control',
     [GP + 'Correctness/ExplicateCorrect.agda']),

    # not in the totals: the public theorem statements (see the audit-surface
    # table)
    ('thm', 'theorem statements', ['agda/Theorems/*.agda']),
]

THEOREMS = {'den': 'agda/Theorems/Denotational.agda', 'op': 'agda/Theorems/Simulation.agda',
            'ck': 'agda/Theorems/Interpreter.agda', 'red': 'agda/Theorems/Reduction.agda',
            'adeq': 'agda/Theorems/Adequacy.agda'}


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
          'red': 'reduction semantics + simulation', 'adeq': 'adequacy'}
NAMES = {'den': 'graph model', 'op': 'simulation', 'ck': 'interpreter',
         'red': 'reduction', 'adeq': 'adequacy'}
EXTRA = 'shared modules not used by all four proofs'


def sides_of(side):
    """The proofs a group belongs to: 'op+red' is counted in both."""
    return side.split('+')


def main():
    seen, counts, files_of = {}, {}, {}
    for side, name, pats in GROUPS:
        files = sorted({f for p in pats for f in glob.glob(p)})
        if not files:
            if side in ('ck', 'red'):
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
           for s in SIDES + ('adeq',)}
    exp = {u for u, (side, _) in group_of.items() if side == 'exp'}
    infra = {u for u, (side, _) in group_of.items() if side == 'infra'}
    reach = {s: reachable(own[s], graph) for s in own}

    # Infrastructure is language independent: it imports only infrastructure.
    bad = sorted(u for u in reachable(infra, graph) - infra)
    if bad:
        sys.exit('infrastructure imports modules that are not infrastructure:\n  '
                 + '\n  '.join(bad))

    # The proofs must be independent: no proof reaches another proof's modules
    # nor adequacy's, nor an experiment (adequacy, examples and the
    # experiments may use anything).
    for s in SIDES:
        for t in SIDES + ('adeq',):
            bad = sorted(reach[s] & (own[t] - own[s])) if s != t else []
            if bad:
                sys.exit(f'{NAMES[s]} imports {NAMES[t]} modules:\n  ' + '\n  '.join(bad))
        bad = sorted(reach[s] & exp)
        if bad:
            sys.exit(f'{NAMES[s]} imports experiment modules:\n  ' + '\n  '.join(bad))

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

    rows = ['semantics of the languages', 'enclose', 'optimize', 'concretize',
            'delay', 'globalize', 'rco', 'lift locals', 'explicate control',
            'select instructions',
            'composition']
    total = {side: 0 for side in SIDES}
    print('| component | ' + ' | '.join(LABELS[s] for s in SIDES) + ' |')
    print('|---|' + '---:|' * len(SIDES))
    for r in rows:
        cells = []
        for side in SIDES:
            n = counts.get((side, r))
            total[side] += n or 0
            cells.append(str(n) if n is not None else '—')
        print(f'| {r} | ' + ' | '.join(cells) + ' |')
    cells = []
    for side in SIDES:
        n = sum(ulines(u) for u in extra[side])
        total[side] += n
        cells.append(str(n) if extra[side] else '—')
    print(f'| {EXTRA} | ' + ' | '.join(cells) + ' |')
    print('| **total** | ' + ' | '.join(f'**{total[side]}**' for side in SIDES) + ' |')
    print()

    def lines(us):
        return sum(ulines(u) for u in us)
    print('| language-independent infrastructure (not in the totals) | lines | '
          + ' | '.join(f'used by {LABELS[s]}' for s in SIDES) + ' |')
    print('|---|---:|' + '---:|' * len(SIDES))
    itotal = {s: 0 for s in SIDES}
    for side, name, _ in GROUPS:
        if side == 'infra':
            us = {unit(f) for f in files_of[(side, name)]}
            cells = []
            for s in SIDES:
                n = lines(u for u in us if u in reach[s])
                itotal[s] += n
                cells.append(str(n) if n else '—')
            print(f'| {name} | {counts[(side, name)]} | ' + ' | '.join(cells) + ' |')
    print(f'| **total** | **{lines(infra)}** | '
          + ' | '.join(f'**{itotal[s]}**' for s in SIDES) + ' |')
    print()
    print(f"Adequacy uses {lines(infra & reach['adeq'])} lines of the infrastructure, "
          f"{lines(infra & reach['adeq'] - reach['den'])} of them not used by the denotational proof.")
    print()
    print('| adequacy (denotational side only) | lines |')
    print('|---|---:|')
    adeq = 0
    for side, name, _ in GROUPS:
        if side == 'adeq':
            adeq += counts[(side, name)]
            print(f'| {name} | {counts[(side, name)]} |')
    n = sum(ulines(u) for u in extra['adeq'])
    adeq += n
    print(f'| {EXTRA}, nor by the denotational one | {n if extra["adeq"] else "—"} |')
    print(f'| **total** | **{adeq}** |')
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
    ALL = ('den', 'op', 'ck', 'red', 'adeq')
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
            'red': 'reduction semantics, machines of Imp, CFG and X86, transition systems'}
    sem_files = {s: {f for f in sreach[s] if kind(f) == 'semantics'} for s in ALL}
    for s in SIDES:
        fs = sem_files[s]
        print(f'| {NAMES[s]}: {SEMS[s]} | {flines(fs)} | '
              + ' | '.join(str(flines(sem_files[t] & fs)) if sem_files[t] & fs else '—' for t in ALL) + ' |')
    for s in ALL:
        print(f'| {NAMES[s]}: theorem statements | {code_lines(THEOREMS[s])} | '
              + ' | '.join(str(code_lines(THEOREMS[s])) if t == s else '—' for t in ALL) + ' |')
    tot = {s: flines(sreach[s] - (thm - {THEOREMS[s]})) for s in ALL}
    alls = surface
    print(f'| **total** | **{flines(alls)}** | ' + ' | '.join(f'**{tot[s]}**' for s in ALL) + ' |')
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
        users = [NAMES[s] for s in SIDES + ('adeq',) if u in reach[s]]
        tag = 'all four proofs' if u in by_all else (', '.join(users) or 'no proof')
        name = ('proof.' if not os.path.exists(u) else '') + modname(u)
        print(f'| `{name}`{split_mark(u) if os.path.exists(u) else ""} | {ulines(u)} | {tag} |')
    print()
    nall = sum(ulines(u) for u in by_all)
    print('| infrastructure module | lines | used by |')
    print('|---|---:|---|')
    for u in sorted(infra):
        users = [NAMES[s] for s in SIDES + ('adeq',) if u in reach[s]]
        name = ('proof.' if not os.path.exists(u) else '') + modname(u)
        print(f'| `{name}`{split_mark(u) if os.path.exists(u) else ""} | {ulines(u)} | '
              f'{", ".join(users) or "no proof"} |')
    print()
    print(f'Shared by all four proofs, not counted: {len(by_all)} modules, {nall} lines.')
    for s in SIDES + ('adeq',):
        print(f'Counted in {NAMES[s]}: {mods(extra[s])}.')
    if unused:
        print(f'Shared but used by no proof: {mods(unused)}.')
    print(f"Examples, not counted: {counts[('examples', 'examples')]} lines.")
    print(f"Module (+ proof/): the definitions are on the audit surface, the lemmas "
          f"in its proof/ half; the lines are those of both.")


if __name__ == '__main__':
    main()
