#!/usr/bin/env python3
"""Count code lines of the three compiler-correctness proofs.

Run from the repository root:  python3 papers/PLDI-2027/loc.py

A code line is a line that is not blank and not a comment ({- -} blocks,
-- line comments).  Every .agda file under agda/ (except agda/old/ and
All.agda) must belong to exactly one group; the script fails otherwise,
so new modules cannot go uncounted.  A group of the CakeML-style side may
have no files yet (a pass not yet proved); it is shown as —.

Totals come from the import graph (`import`/`open import` lines, with or
without `as`, `using`, module arguments or `public`).  A proof's total is
its own modules plus the shared modules it reaches transitively that are
not reached by all three proofs; shared modules reached by all three are
not counted anywhere.  Adequacy, an add-on to the denotational proof, also
counts the shared modules it reaches that the denotational total does not
already count.  The script also fails if one proof reaches another proof's
modules, or adequacy's.
"""
import glob, os, re, sys

G = 'agda/Compiler/Model/Graph/'
O = 'agda/Compiler/Operational/'
F = 'agda/Compiler/Functional/'

# (side, group, glob patterns)
GROUPS = [
    # also the machine-independent lemmas both operational styles use:
    # Lang/{ListUtil,Scope,ScopeRename,Rename},
    # Compile/{EncloseScope,GlobalizeTable,PipelineScope},
    # and the observations (Observation.agda).  Those not used by all three
    # proofs are counted in each proof that uses them (see main).
    ('shared', 'syntax, languages, compiler passes',
     ['agda/abt/*.agda', 'agda/Compiler/Lang/*.agda', 'agda/Compiler/Compile/*.agda',
      'agda/Compiler/Observation.agda',
      'agda/Primitives.agda', 'agda/NewSigUtil.agda', 'agda/NewSyntaxUtil.agda']),

    ('den', 'generic infrastructure',
     ['agda/SetsAsPredicates.agda', 'agda/NewSemantics.agda', 'agda/NewDOpSig.agda',
      'agda/NewEnv.agda', 'agda/NewDenotProperties.agda']),
    ('den', 'domain, operators, continuity', [G + 'Domain/ISWIM/*.agda']),
    ('den', 'semantics of the languages',
     [G + 'Sem/ISWIM.agda', G + 'Sem/Clos2Iswim.agda', G + 'Sem/Clos3Iswim.agda',
      G + 'Sem/Clos3IswimContinuous.agda', G + 'Sem/Clos4Iswim.agda',
      G + 'Sem/Clos4IswimContinuous.agda', G + 'Sem/Clos5Iswim.agda',
      G + 'Sem/Clos5IswimContinuous.agda', G + 'Sem/Continuous.agda', G + 'Sem/RenameSem.agda',
      G + 'Sem/Imp.agda']),
    ('den', 'enclose', [G + 'Correctness/EncloseCorrect.agda']),
    ('den', 'optimize', [G + 'Correctness/OptimizeCorrect.agda']),
    ('den', 'concretize', [G + 'Correctness/ConcretizeCorrect.agda']),
    ('den', 'delay',
     [G + 'Correctness/DelayFiniteCommon.agda', G + 'Correctness/DelayFiniteRel.agda',
      G + 'Correctness/DelayApp.agda', G + 'Correctness/DelayPreserve.agda',
      G + 'Correctness/DelayReflectFinite.agda']),
    ('den', 'globalize', [G + 'Correctness/GlobalizeCorrect.agda']),
    # each rco module also proves compile-mon (compile then rco) end to end
    ('den', 'rco', [G + 'Correctness/RCOCorrect.agda']),
    ('den', 'lift locals', [G + 'Correctness/LiftLocalsCorrect.agda']),
    ('den', 'composition', [G + 'Correctness/CompilerCorrect.agda']),

    ('op', 'generic infrastructure',
     [O + 'Smallstep.agda', O + 'Simulation.agda']),
    ('op', 'semantics of the languages', [O + 'Machine/*.agda']),
    ('op', 'enclose', [O + 'Correctness/EncloseSim.agda']),
    ('op', 'optimize', [O + 'Correctness/OptimizeSim.agda']),
    ('op', 'concretize', [O + 'Correctness/ConcretizeSim.agda']),
    ('op', 'delay', [O + 'Correctness/DelaySim.agda']),
    ('op', 'globalize', [O + 'Correctness/GlobalizeSim.agda']),
    ('op', 'rco', [O + 'Correctness/RCOSim.agda']),
    ('op', 'lift locals', [O + 'Correctness/LiftLocalsSim.agda']),
    ('op', 'composition', [O + 'Correctness/CompilerSim.agda']),

    ('ck', 'generic infrastructure', [F + 'Clock.agda']),
    ('ck', 'semantics of the languages', [F + 'Interp/*.agda']),
    ('ck', 'enclose', [F + 'Correctness/EncloseFuel.agda']),
    ('ck', 'optimize', [F + 'Correctness/OptimizeFuel.agda']),
    ('ck', 'concretize', [F + 'Correctness/ConcretizeFuel.agda']),
    ('ck', 'delay', [F + 'Correctness/DelayFuel.agda']),
    ('ck', 'globalize', [F + 'Correctness/GlobalizeFuel.agda']),
    ('ck', 'rco', [F + 'Correctness/RCOFuel.agda']),
    ('ck', 'lift locals', [F + 'Correctness/LiftLocalsFuel.agda']),
    ('ck', 'composition', [F + 'Correctness/CompilerFuel.agda']),

    ('adeq', 'ISWIM',
     [O + 'Adequacy/Common.agda', O + 'Adequacy/Soundness.agda', O + 'Adequacy/LogRel.agda',
      O + 'Adequacy/ISWIM.agda', G + 'Sem/ISWIMContinuous.agda']),
    ('adeq', 'Clos5',
     [O + 'Adequacy/Clos5Common.agda', O + 'Adequacy/Clos5Soundness.agda', O + 'Adequacy/Clos5LogRel.agda',
      O + 'Adequacy/Clos5.agda']),
    ('adeq', 'well-formedness of compiled programs',
     [O + 'Adequacy/Clos5WF.agda', O + 'Adequacy/CompileWF.agda']),
    ('adeq', 'end to end', [O + 'Adequacy/EndToEnd.agda']),

    ('examples', 'examples',
     [G + 'Correctness/*Example.agda', 'agda/Compiler/Compile/Examples/*.agda']),

    # not in the totals: a direct backward simulation for delay, without
    # determinism, for comparison (see loc.md)
    ('exp', 'CompCert-style: direct backward simulation for delay — framework',
     [O + 'Backward.agda']),
    ('exp', 'CompCert-style: direct backward simulation for delay — delay',
     [O + 'Correctness/DelayBackSim.agda']),
]


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


def code_lines(path):
    text = strip_comments(open(path, encoding='utf-8').read())
    return sum(1 for line in text.split('\n') if line.strip())


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


def reachable(roots, graph):
    seen, todo = set(), list(roots)
    while todo:
        f = todo.pop()
        if f not in seen:
            seen.add(f)
            todo.extend(graph[f])
    return seen


SIDES = ('den', 'op', 'ck')
NAMES = {'den': 'denotational', 'op': 'CompCert-style', 'ck': 'CakeML-style',
         'adeq': 'adequacy'}
EXTRA = 'shared modules not used by all three proofs'


def main():
    seen, counts, files_of = {}, {}, {}
    for side, name, pats in GROUPS:
        files = sorted({f for p in pats for f in glob.glob(p)})
        if not files:
            if side == 'ck':
                continue
            sys.exit(f'no files for group {side}/{name}')
        for f in files:
            if f in seen:
                sys.exit(f'{f} is in two groups')
            seen[f] = (side, name)
        files_of[(side, name)] = files
        counts[(side, name)] = sum(code_lines(f) for f in files)
    every = {f for f in glob.glob('agda/**/*.agda', recursive=True)
             if not f.startswith('agda/old/') and f != 'agda/All.agda'}
    missing = sorted(every - set(seen))
    if missing:
        sys.exit('not in any group:\n  ' + '\n  '.join(missing))

    graph = {f: imports(f) for f in every}
    own = {s: {f for f, (side, _) in seen.items() if side == s}
           for s in SIDES + ('adeq',)}
    reach = {s: reachable(own[s], graph) for s in own}

    # The proofs must be independent: no proof reaches another proof's modules
    # nor adequacy's (adequacy, examples and the experiments may use anything).
    for s in SIDES:
        for t in SIDES + ('adeq',):
            bad = sorted(reach[s] & own[t]) if s != t else []
            if bad:
                sys.exit(f'{NAMES[s]} imports {NAMES[t]} modules:\n  ' + '\n  '.join(bad))

    shared = {f for f, (side, _) in seen.items() if side == 'shared'}
    by_all = shared & reach['den'] & reach['op'] & reach['ck']
    extra = {s: sorted((shared & reach[s]) - by_all) for s in SIDES}
    # Adequacy is an add-on to the denotational proof, so shared modules that
    # the denotational proof already counts are not counted again.
    extra['adeq'] = sorted((shared & reach['adeq']) - by_all - set(extra['den']))
    unused = sorted(shared - set().union(*(reach[s] for s in own)))

    rows = ['generic infrastructure', 'domain, operators, continuity',
            'semantics of the languages', 'enclose', 'optimize', 'concretize',
            'delay', 'globalize', 'rco', 'lift locals', 'composition']
    total = {side: 0 for side in SIDES}
    print('| component | denotational | CompCert-style | CakeML-style |')
    print('|---|---:|---:|---:|')
    for r in rows:
        cells = []
        for side in SIDES:
            n = counts.get((side, r))
            total[side] += n or 0
            cells.append(str(n) if n is not None else '—')
        print(f'| {r} | ' + ' | '.join(cells) + ' |')
    cells = []
    for side in SIDES:
        n = sum(code_lines(f) for f in extra[side])
        total[side] += n
        cells.append(str(n) if extra[side] else '—')
    print(f'| {EXTRA} | ' + ' | '.join(cells) + ' |')
    print('| **total** | ' + ' | '.join(f'**{total[side]}**' for side in SIDES) + ' |')
    print()
    print('| adequacy (denotational side only) | lines |')
    print('|---|---:|')
    adeq = 0
    for side, name, _ in GROUPS:
        if side == 'adeq':
            adeq += counts[(side, name)]
            print(f'| {name} | {counts[(side, name)]} |')
    n = sum(code_lines(f) for f in extra['adeq'])
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

    def mods(fs):
        return ', '.join(f'`{f[len("agda/"):-len(".agda")].replace("/", ".")}` ({code_lines(f)})'
                         for f in fs) or 'none'
    print('| shared module | lines | used by |')
    print('|---|---:|---|')
    for f in sorted(shared):
        users = [NAMES[s] for s in SIDES + ('adeq',) if f in reach[s]]
        tag = 'all three proofs' if f in by_all else (', '.join(users) or 'no proof')
        print(f'| `{f[len("agda/"):-len(".agda")].replace("/", ".")}` | {code_lines(f)} | {tag} |')
    print()
    nall = sum(code_lines(f) for f in by_all)
    print(f'Shared by all three proofs, not counted: {len(by_all)} modules, {nall} lines.')
    for s in SIDES + ('adeq',):
        print(f'Counted in {NAMES[s]}: {mods(extra[s])}.')
    if unused:
        print(f'Shared but used by no proof: {mods(unused)}.')
    print(f"Examples, not counted: {counts[('examples', 'examples')]} lines.")


if __name__ == '__main__':
    main()
