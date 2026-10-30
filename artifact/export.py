#!/usr/bin/env python3
"""Export the anonymized artifact of the PLDI 2027 paper: ISWIMμ (agda/Mu/).

    python3 artifact/export.py OUTDIR        (from the repository root)

OUTDIR must not exist, or be empty.  The artifact gets

  * the import closure of agda/Mu/All.agda and agda/AllScott.agda (and so
    none of the other pipelines, agda/old/, agda/Mu/Experiments.agda or
    agda/Mu/proof/Mixed/), at the same paths under agda/, so that the
    paper's "Agda:" lines (paths relative to agda/) stay valid;
  * the TypeTopology modules in that closure, vendored, already patched
    with scott/typetopology-builtin-alias.patch, under vendor/TypeTopology/,
    with TypeTopology's LICENSE, the patch and a NOTICE;
  * loc.py (papers/PLDI-2027/loc.py, run with --artifact by `make tables`),
    and the README, Makefile and Dockerfile of artifact/template/.

TypeTopology is taken from _deps/TypeTopology, fetched and patched by
`make scott-deps`; the script checks that it is at the pinned commit and
patched.

Comments that would identify the authors are rewritten on the way (see
REWRITES), and the script fails if the exported tree still contains an
identifying string (see BANNED), or if a rewrite no longer applies.  It
also lists the paths that comments mention but that are not in the
artifact (informational).
"""
import hashlib, os, re, shutil, subprocess, sys

REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
ROOTS = ['agda/Mu/All.agda', 'agda/AllScott.agda']
EXCLUDED = ['agda/Mu/Experiments.agda', 'agda/Mu/proof/Mixed/', 'agda/old/', 'agda/Untyped/']
TT = os.path.join(REPO, '_deps', 'TypeTopology')
TT_COMMIT = '17487fc910f3bb305c30001507fed5d41d52dc3c'
TT_URL = 'https://github.com/martinescardo/TypeTopology'
PATCH = os.path.join(REPO, 'scott', 'typetopology-builtin-alias.patch')
TEMPLATE = os.path.join(REPO, 'artifact', 'template')
LOC = os.path.join(REPO, 'papers', 'PLDI-2027', 'loc.py')


# --- the import closure --------------------------------------------------------

def strip_comments(s):
    """s without {- -} blocks and -- line comments (newlines kept)."""
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
    return '\n'.join(re.sub(r'(^|\s)--.*$', '', line) for line in ''.join(out).split('\n'))


IMPORT = re.compile(r'(?<![^\s;{(])(?:open\s+)?import\s+([^\s;(){}]+)')


def code_of(path):
    text = open(path, encoding='utf-8').read()
    if path.endswith('.lagda'):
        text = '\n'.join(re.findall(r'\\begin\{code\}(.*?)\\end\{code\}', text, re.S))
    return strip_comments(text)


def resolve(mod):
    """The file of module mod, in agda/ or TypeTopology's source/; None for a
    module of the standard library or Agda's builtins."""
    rel = mod.replace('.', '/')
    for root in (os.path.join(REPO, 'agda'), os.path.join(TT, 'source')):
        for ext in ('.agda', '.lagda'):
            f = os.path.join(root, rel + ext)
            if os.path.exists(f):
                return f
    return None


def closure():
    seen, todo = set(), [os.path.join(REPO, r) for r in ROOTS]
    while todo:
        f = todo.pop()
        if f in seen:
            continue
        seen.add(f)
        for m in IMPORT.findall(code_of(f)):
            g = resolve(m)
            if g and g not in seen:
                todo.append(g)
    agda = sorted(os.path.relpath(f, REPO) for f in seen if f.startswith(os.path.join(REPO, 'agda') + os.sep))
    tt = sorted(os.path.relpath(f, TT) for f in seen if f.startswith(TT + os.sep))
    return agda, tt


# --- rewrites for anonymity ----------------------------------------------------

# (file or None for every Agda file, pattern, replacement, expected matches
# (None: any number, at least one over all files))
ABT = (r'Extracted from the abt library \(github\.com/jsiek/abstract-binding-trees,\s*commit 1387c40\)',
       'Extracted from a library of abstract binding trees (not named, for\n   anonymous review)')
REWRITES = [
    (None, ABT[0], ABT[1], None),
    ('agda/Mu/All.agda',
     r'\n  The experiment of mixing semantics is not part of the paper; it is\n'
     r'  checked from Mu/Experiments\.agda\.\n', '', 1),
    ('agda/Mu/All.agda',
     r'  agda/Mu/ mirrors agda/: Mu/X\.agda corresponds to X\.agda \(with\n'
     r'  Language/Typed/ as Mu/Language/ and Semantics/<style>/Typed/ as\n'
     r'  Mu/Semantics/<style>/\), and the module Mu\.X to X\. It reuses the\n'
     r'  frameworks of agda/Framework/ unchanged;',
     '  ISWIMμ uses the language-independent frameworks of agda/Framework/\n'
     '  (and their lemmas, agda/proof/Framework/);', 1),
    ('agda/Mu/proof/Adequacy/ISWIM.agda',
     r'graph model\'s end-to-end theorem \(Mu/proof/Adequacy/EndToEnd\.agda\),\n'
     r'  and the bridge at ISWIMμ of the mixed proof, which joins a pass\n'
     r'  proved in the graph model to passes proved by the interpreters\n'
     r'  \(Mu/proof/Mixed/CompilerMixed\.agda\)\.',
     "graph model's end-to-end theorem (Mu/proof/Adequacy/EndToEnd.agda).", 1),
    ('agda/Mu/proof/Compiler/HoistOlder.agda',
     r'older ones only\n  \(as Untyped/Semantics/Graph/Clos5Iswim\.agda does\), so it needs',
     'older ones only,\n  so it needs', 1),
    ('agda/Framework/GraphModel/Prelude.agda', r'papers/PLDI-2027/loc\.py', 'loc.py', 1),
    ('agda/AllScott.agda',
     r'  which fetches TypeTopology \(scott/fetch-typetopology\.sh\) and runs\n'
     r'  scott/check\.sh on this file\.',
     '  (from the root of the artifact), which checks it with the\n'
     '  TypeTopology vendored in vendor/TypeTopology/.', 1),
]

# loc.py's comments: the untyped pipeline is not described by its history
LOC_REWRITES = [
    (r'the preserved untyped pipeline', 'the untyped pipeline', 1),
    (r"'untyped pipeline \(preserved\)'", "'untyped pipeline'", 1),
    (r'the untyped pipeline, preserved ', 'the untyped pipeline ---------', 1),
    (r'the preserved untyped one', 'the untyped one', 1),
]

# agda/Mu/README.md, the road map: the checking section is the artifact's,
# and the experiments that the artifact leaves out are not mentioned
README_REWRITES = [
    (r'## Checking\n.*?(?=## Layout)',
     '## Checking\n\n'
     'From the root of the artifact (see `../../README.md`):\n\n'
     '* `make check` checks the graph model, abstract machines, clocked\n'
     '  interpreters, reduction semantics and adequacy\n'
     '  ([`All.agda`](All.agda)) with `--safe`, and then runs\n'
     '  `make pragma-check`. It needs Agda 2.8.0 and the standard library\n'
     '  2.4.\n'
     '* `make check-scott` checks the Scott-domain development\n'
     '  (`../AllScott.agda`) with `--safe`. It needs TypeTopology, which the\n'
     '  artifact vendors, patched, in `../../vendor/TypeTopology/`.\n'
     '* `make pragma-check` fails if any checked file has a `postulate` or a\n'
     '  pragma, other than the `--without-K` option of the abt extract.\n'
     '* `make tables` prints Tables 1 and 2 of the paper\n'
     '  (`python3 loc.py --artifact`).\n\n', 1),
    (r'\| Table 1 \(lines of the five proofs\) \| `\.\./\.\./papers/PLDI-2027/loc\.py` \|[^\n]*\n'
     r'\| Table 2 \(infrastructure\) \| `\.\./\.\./papers/PLDI-2027/loc\.py` \|[^\n]*\n',
     '| Table 1 (lines of the five proofs) | `../../loc.py` | `make tables` (`python3 loc.py --artifact`) |\n'
     '| Table 2 (infrastructure) | `../../loc.py` | `make tables` (`python3 loc.py --artifact`) |\n', 1),
    (r'`python3 papers/PLDI-2027/loc\.py --mu` checks this and prints the size\n'
     r'of each style\'s surface \(the Scott column\'s is the closure of\n'
     r'`Theorems/ScottDomains\.agda`, which needs TypeTopology\)\.',
     '`make tables` (`python3 loc.py --artifact`) checks this.', 1),
    (r'The language-independent definitions are shared with the other\n'
     r'pipelines of the repository and live in',
     'The language-independent definitions live in', 1),
]


def rewrite(rel, text, used):
    for f, pat, rep, n in REWRITES:
        if f is not None and f != rel:
            continue
        text, k = re.subn(pat, rep, text)
        if n is not None and k != n:
            sys.exit(f'export: rewrite {pat!r} matched {k} times in {rel}, expected {n}')
        used[pat] = used.get(pat, 0) + k
    return text


# --- the check for anonymity ---------------------------------------------------

BANNED = [r'jsiek', r'siek', r'jeremy', r'iu\.edu', r'indiana', r'PR #', r'pull request',
          r'(?<![\w&])#[0-9]+\b', r'github\.com(?!/agda/|/martinescardo/TypeTopology)']
# TypeTopology is third-party: it may name its own repository and issues; it
# must not name us
BANNED_TT = [r'jsiek', r'siek', r'iu\.edu', r'indiana']


def anonymity_check(out):
    bad = []
    for root, _, files in os.walk(out):
        for name in files:
            path = os.path.join(root, name)
            rel = os.path.relpath(path, out)
            pats = BANNED_TT if rel.startswith('vendor' + os.sep) and rel != os.path.join(
                'vendor', 'TypeTopology', 'NOTICE') else BANNED
            try:
                text = open(path, encoding='utf-8').read()
            except UnicodeDecodeError:
                continue
            for i, line in enumerate(text.split('\n'), 1):
                for p in pats:
                    if re.search(p, line, re.I if p.islower() else 0):
                        bad.append(f'{rel}:{i}: {line.strip()}')
            if re.search(r'siek|jeremy', name, re.I):
                bad.append(rel)
    if bad:
        sys.exit('export: identifying strings in the artifact:\n  ' + '\n  '.join(bad))


def dangling(out):
    """Paths ending in .agda that comments of the exported Agda files mention
    but that are not in the artifact (relative to agda/, agda/Mu/, the
    mentioning file's directory, or the artifact's root)."""
    refs = {}
    for root, _, files in os.walk(os.path.join(out, 'agda')):
        for name in files:
            path = os.path.join(root, name)
            for m in re.finditer(r'[\w./<>-]+\.agda', open(path, encoding='utf-8').read()):
                r = m.group(0)
                if '<' in r or '*' in r:
                    continue
                cands = [os.path.join(out, 'agda', r), os.path.join(out, 'agda', 'Mu', r),
                         os.path.join(root, r), os.path.join(out, r),
                         os.path.join(out, 'agda', 'proof', r), os.path.join(out, 'agda', 'Mu', 'proof', r)]
                if not any(os.path.exists(c) for c in cands):
                    refs.setdefault(r, set()).add(os.path.relpath(path, out))
    return refs


# --- the export -----------------------------------------------------------------

def tt_checked():
    """TypeTopology is at the pinned commit, with the patch applied."""
    if not os.path.isfile(os.path.join(TT, '.fetched-' + TT_COMMIT)):
        sys.exit(f'export: {TT} is not fetched at {TT_COMMIT}: run `make scott-deps` first')
    head = subprocess.run(['git', '-C', TT, 'rev-parse', 'HEAD'], capture_output=True, text=True).stdout.strip()
    if head != TT_COMMIT:
        sys.exit(f'export: {TT} is at {head}, not {TT_COMMIT}')
    r = subprocess.run(['git', '-C', TT, 'apply', '--reverse', '--check', PATCH], capture_output=True, text=True)
    if r.returncode != 0:
        sys.exit(f'export: the patch is not applied in {TT}:\n{r.stderr}')
    st = subprocess.run(['git', '-C', TT, 'status', '--porcelain', '--untracked-files=no'],
                        capture_output=True, text=True).stdout.split('\n')
    changed = sorted(l[3:] for l in st if l.strip())
    patched = sorted(re.findall(r'^\+\+\+ b/(\S+)', open(PATCH, encoding='utf-8').read(), re.M))
    if changed != patched:
        sys.exit(f'export: {TT} has changes other than the patch: {changed}')


NOTICE = f"""TypeTopology (vendored subset)
==============================

This directory holds the modules of TypeTopology that the Scott-domain
development imports, transitively (agda/AllScott.agda), and nothing else:
{{n}} of its source files, under source/, at their paths in TypeTopology.

Origin:  {TT_URL}
Commit:  {TT_COMMIT}
License: see LICENSE (TypeTopology's own, unchanged).
Authors: Martin Escardo and the TypeTopology contributors; its domain
         theory (source/DomainTheory/) is by Tom de Jong.

The files are unchanged except that the patch
typetopology-builtin-alias.patch (in this directory) has been applied to
them.  It makes TypeTopology's natural numbers, Booleans and lists the
builtin ones of Agda.Builtin.* (as the standard library's are), and drops
its NATPLUS and NATTIMES pragmas, so that a module may import both the
standard library and TypeTopology.  It changes these files:

{{patched}}

typetopology.agda-lib is TypeTopology's library file, unchanged.
"""

LOC_DOC = '''"""Count code lines of the compiler-correctness proofs of the artifact.

Run from the root of the artifact:  python3 loc.py --artifact
(or `make tables`), which prints Tables 1 and 2 of the paper.

This is the script that measures the full development; the artifact holds
only ISWIMμ's part of it (the import closure of agda/Mu/All.agda and
agda/AllScott.agda), so it is run with --artifact.  In that mode the
groups of modules that belong to the other parts are empty and skipped,
and the checks about them are skipped too; the checks about ISWIMμ still
run (every module is in exactly one group, no proof reaches another's
modules, the audit surface imports no proof module).

A code line is a line that is not blank, not a comment ({- -} blocks,
-- line comments) and not part of an import statement (`import` or
`open import`, with its continuation lines): imports depend on how
finely a development is split into modules, not on its content.

A proof's total is its own modules plus the shared modules it reaches
(transitively, through imports) that are not reached by all four of the
graph model, abstract machines, clocked interpreters and reduction
semantics; shared modules reached by all four (ISWIMμ's languages and
passes) are counted in no total.  Language-independent infrastructure is
counted separately (Table 2), for each proof the infrastructure modules
it reaches.  A module X.agda and its proof half proof/X.agda are one
unit.  For the Scott column, the infrastructure is agda/Framework/Scott/
and agda/proof/Framework/Scott/ (domain theory on TypeTopology), and
TypeTopology's domain theory is the modules under DomainTheory/ and
Lifting/ of vendor/TypeTopology/source/ that the column imports; the
rest of TypeTopology it imports (its foundations) is counted for no
column.
"""'''


def main():
    if len(sys.argv) != 2:
        sys.exit(__doc__)
    out = os.path.abspath(sys.argv[1])
    if os.path.exists(out) and os.listdir(out):
        sys.exit(f'export: {out} exists and is not empty')
    os.chdir(REPO)
    tt_checked()
    agda, tt = closure()
    for f in agda:
        for e in EXCLUDED:
            if f == e or (e.endswith('/') and f.startswith(e)):
                sys.exit(f'export: {f} is in the import closure, but is excluded')
    os.makedirs(out, exist_ok=True)

    used = {}
    for rel in agda:
        text = rewrite(rel, open(rel, encoding='utf-8').read(), used)
        dst = os.path.join(out, rel)
        os.makedirs(os.path.dirname(dst), exist_ok=True)
        open(dst, 'w', encoding='utf-8').write(text)
    for f, pat, _, n in REWRITES:
        if not used.get(pat):
            sys.exit(f'export: rewrite {pat!r} matched nowhere')

    # the road map
    text = open('agda/Mu/README.md', encoding='utf-8').read()
    for pat, rep, n in README_REWRITES:
        text, k = re.subn(pat, rep, text, flags=re.S)
        if k != n:
            sys.exit(f'export: README rewrite {pat!r} matched {k} times, expected {n}')
    open(os.path.join(out, 'agda/Mu/README.md'), 'w', encoding='utf-8').write(text)

    # TypeTopology
    vt = os.path.join(out, 'vendor', 'TypeTopology')
    for rel in tt:
        dst = os.path.join(vt, rel)
        os.makedirs(os.path.dirname(dst), exist_ok=True)
        shutil.copyfile(os.path.join(TT, rel), dst)
    for f in ('LICENSE', 'typetopology.agda-lib'):
        shutil.copyfile(os.path.join(TT, f), os.path.join(vt, f))
    shutil.copyfile(PATCH, os.path.join(vt, 'typetopology-builtin-alias.patch'))
    patched = re.findall(r'^\+\+\+ b/(\S+)', open(PATCH, encoding='utf-8').read(), re.M)
    open(os.path.join(vt, 'NOTICE'), 'w', encoding='utf-8').write(
        NOTICE.format(n=len(tt), patched='\n'.join('  ' + p for p in patched)))

    # loc.py and the template (README, Makefile, Dockerfile, library file)
    loc = open(LOC, encoding='utf-8').read()
    if not loc.startswith('#!/usr/bin/env python3\n"""'):
        sys.exit('export: loc.py does not start with its docstring')
    end = loc.index('"""', len('#!/usr/bin/env python3\n"""')) + 3
    loc = loc[end:]
    for pat, rep, n in LOC_REWRITES:
        loc, k = re.subn(pat, rep, loc)
        if k != n:
            sys.exit(f'export: loc.py rewrite {pat!r} matched {k} times, expected {n}')
    open(os.path.join(out, 'loc.py'), 'w', encoding='utf-8').write('#!/usr/bin/env python3\n' + LOC_DOC + loc)
    for f in sorted(os.listdir(TEMPLATE)):
        shutil.copyfile(os.path.join(TEMPLATE, f), os.path.join(out, f))

    # Tables 1 and 2, measured on the exported tree, into the README
    r = subprocess.run([sys.executable, 'loc.py', '--artifact'], cwd=out, capture_output=True, text=True)
    if r.returncode != 0:
        sys.exit(f'export: loc.py --artifact fails on the exported tree:\n{r.stdout}{r.stderr}')
    readme = os.path.join(out, 'README.md')
    text = open(readme, encoding='utf-8').read()
    if text.count('TABLES_OUTPUT') != 1:
        sys.exit('export: the README has no TABLES_OUTPUT')
    text = text.replace('TABLES_OUTPUT', r.stdout.strip().replace('## ', '#### '))
    open(readme, 'w', encoding='utf-8').write(text)
    shutil.rmtree(os.path.join(out, '__pycache__'), ignore_errors=True)

    anonymity_check(out)

    # a manifest, and a summary
    lines, nbytes = [], 0
    for root, _, files in os.walk(out):
        for name in files:
            path = os.path.join(root, name)
            data = open(path, 'rb').read()
            nbytes += len(data)
            lines.append(f'{hashlib.sha256(data).hexdigest()}  {os.path.relpath(path, out)}')
    open(os.path.join(out, 'MANIFEST.sha256'), 'w').write('\n'.join(sorted(lines, key=lambda l: l[66:])) + '\n')
    print(f'exported to {out}: {len(agda)} Agda files of ours, {len(tt)} of TypeTopology, '
          f'{len(lines)} files in all, {nbytes // 1024} KiB')
    refs = dangling(out)
    if refs:
        print('paths mentioned in comments but not in the artifact (informational):')
        for r in sorted(refs):
            print(f'  {r}  (in {", ".join(sorted(refs[r]))})')


if __name__ == '__main__':
    main()
