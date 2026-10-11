#!/usr/bin/env python3
"""Count code lines of the three compiler-correctness proofs.

Run from the repository root:  python3 papers/PLDI-2027/loc.py

A code line is a line that is not blank and not a comment ({- -} blocks,
-- line comments).  Every .agda file under agda/ (except agda/old/ and
All.agda) must belong to exactly one group; the script fails otherwise,
so new modules cannot go uncounted.  A group of the CakeML-style side may
have no files yet (a pass not yet proved); it is shown as —.
"""
import glob, os, re, sys

G = 'agda/Compiler/Model/Graph/'
O = 'agda/Compiler/Operational/'
F = 'agda/Compiler/Functional/'

# (side, group, glob patterns)
GROUPS = [
    ('shared', 'syntax, languages, compiler passes',
     ['agda/abt/*.agda', 'agda/Compiler/Lang/*.agda', 'agda/Compiler/Compile/*.agda',
      'agda/Primitives.agda', 'agda/NewSigUtil.agda', 'agda/NewSyntaxUtil.agda']),

    ('den', 'generic infrastructure',
     ['agda/SetsAsPredicates.agda', 'agda/NewSemantics.agda', 'agda/NewDOpSig.agda',
      'agda/NewEnv.agda', 'agda/NewDenotProperties.agda']),
    ('den', 'domain, operators, continuity', [G + 'Domain/ISWIM/*.agda']),
    ('den', 'semantics of the languages',
     [G + 'Sem/ISWIM.agda', G + 'Sem/Clos2Iswim.agda', G + 'Sem/Clos3Iswim.agda',
      G + 'Sem/Clos3IswimContinuous.agda', G + 'Sem/Clos4Iswim.agda',
      G + 'Sem/Clos4IswimContinuous.agda', G + 'Sem/Clos5Iswim.agda',
      G + 'Sem/Continuous.agda', G + 'Sem/RenameSem.agda']),
    ('den', 'enclose', [G + 'Correctness/EncloseCorrect.agda']),
    ('den', 'optimize', [G + 'Correctness/OptimizeCorrect.agda']),
    ('den', 'concretize', [G + 'Correctness/ConcretizeCorrect.agda']),
    ('den', 'delay',
     [G + 'Correctness/DelayFiniteCommon.agda', G + 'Correctness/DelayFiniteRel.agda',
      G + 'Correctness/DelayApp.agda', G + 'Correctness/DelayPreserve.agda',
      G + 'Correctness/DelayReflectFinite.agda']),
    ('den', 'globalize', [G + 'Correctness/GlobalizeCorrect.agda']),
    ('den', 'composition', [G + 'Correctness/CompilerCorrect.agda']),

    ('op', 'generic infrastructure',
     [O + 'Observation.agda', O + 'Smallstep.agda', O + 'Simulation.agda']),
    ('op', 'semantics of the languages', [O + 'Machine/*.agda']),
    ('op', 'enclose', [O + 'Correctness/EncloseSim.agda']),
    ('op', 'optimize', [O + 'Correctness/OptimizeSim.agda']),
    ('op', 'concretize', [O + 'Correctness/ConcretizeSim.agda']),
    ('op', 'delay', [O + 'Correctness/DelaySim.agda']),
    ('op', 'globalize', [O + 'Correctness/GlobalizeSim.agda']),
    ('op', 'composition', [O + 'Correctness/CompilerSim.agda']),

    ('ck', 'generic infrastructure', [F + 'Clock.agda']),
    ('ck', 'semantics of the languages', [F + 'Interp/*.agda']),
    ('ck', 'enclose', [F + 'Correctness/EncloseFuel.agda']),
    ('ck', 'optimize', [F + 'Correctness/OptimizeFuel.agda']),
    ('ck', 'concretize', [F + 'Correctness/ConcretizeFuel.agda']),
    ('ck', 'delay', [F + 'Correctness/DelayFuel.agda']),
    ('ck', 'globalize', [F + 'Correctness/GlobalizeFuel.agda']),
    ('ck', 'composition', [F + 'Correctness/CompilerFuel.agda']),

    ('adeq', 'ISWIM',
     [O + 'Adequacy/Common.agda', O + 'Adequacy/Soundness.agda', O + 'Adequacy/LogRel.agda',
      O + 'Adequacy/ISWIM.agda', G + 'Sem/ISWIMContinuous.agda']),
    ('adeq', 'Clos5',
     [O + 'Adequacy/Clos5Common.agda', O + 'Adequacy/Clos5Continuous.agda',
      O + 'Adequacy/Clos5Soundness.agda', O + 'Adequacy/Clos5LogRel.agda',
      O + 'Adequacy/Clos5.agda']),
    ('adeq', 'well-formedness of compiled programs',
     [O + 'Adequacy/Scope.agda', O + 'Adequacy/Clos5WF.agda', O + 'Adequacy/CompileWF.agda']),
    ('adeq', 'end to end', [O + 'Adequacy/EndToEnd.agda']),

    ('examples', 'examples', [G + 'Correctness/*Example.agda']),

    # not in the totals: a direct backward simulation for delay, without
    # determinism, for comparison (see loc.md)
    ('exp', 'CompCert-style: direct backward simulation for delay — framework',
     [O + 'Backward.agda']),
    ('exp', 'CompCert-style: direct backward simulation for delay — delay',
     [O + 'Correctness/DelayBackSim.agda']),
]


def code_lines(path):
    s = open(path, encoding='utf-8').read()
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
    n = 0
    for line in ''.join(out).split('\n'):
        line = re.sub(r'(^|\s)--.*$', '', line)
        if line.strip():
            n += 1
    return n


def main():
    seen, counts = {}, {}
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
        counts[(side, name)] = sum(code_lines(f) for f in files)
    every = {f for f in glob.glob('agda/**/*.agda', recursive=True)
             if not f.startswith('agda/old/') and f != 'agda/All.agda'}
    missing = sorted(every - set(seen))
    if missing:
        sys.exit('not in any group:\n  ' + '\n  '.join(missing))

    rows = ['generic infrastructure', 'domain, operators, continuity',
            'semantics of the languages', 'enclose', 'optimize', 'concretize',
            'delay', 'globalize', 'composition']
    sides = ('den', 'op', 'ck')
    total = {side: 0 for side in sides}
    print('| component | denotational | CompCert-style | CakeML-style |')
    print('|---|---:|---:|---:|')
    for r in rows:
        cells = []
        for side in sides:
            n = counts.get((side, r))
            total[side] += n or 0
            cells.append(str(n) if n is not None else '—')
        print(f'| {r} | ' + ' | '.join(cells) + ' |')
    print('| **total** | ' + ' | '.join(f'**{total[side]}**' for side in sides) + ' |')
    print()
    print('| adequacy (denotational side only) | lines |')
    print('|---|---:|')
    adeq = 0
    for side, name, _ in GROUPS:
        if side == 'adeq':
            adeq += counts[(side, name)]
            print(f'| {name} | {counts[(side, name)]} |')
    print(f'| **total** | **{adeq}** |')
    print()
    print('| experiment (not in the totals) | lines |')
    print('|---|---:|')
    for side, name, _ in GROUPS:
        if side == 'exp':
            print(f'| {name} | {counts[(side, name)]} |')
    print()
    print(f"Not counted: shared code ({counts[('shared', 'syntax, languages, compiler passes')]} "
          f"lines: syntax, languages, compiler passes) and examples "
          f"({counts[('examples', 'examples')]} lines).")


if __name__ == '__main__':
    main()
