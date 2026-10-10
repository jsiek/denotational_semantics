# Earlier developments

These are the earlier developments in this repository, moved here from
`agda/` so that `agda/` holds just the closure-conversion compiler
(`agda/All.agda`).

They use the abt library (github.com/jsiek/abstract-binding-trees, at
commit 1387c40), through `denotational-old.agda-lib`. Agda finds the
library from the current directory, so check these files from inside
`agda/old/`, e.g.

    cd agda/old && agda ISWIM.agda

The modules shared with the compiler (`Primitives`, `SetsAsPredicates`,
the `New*` modules, and a few `Compiler.*` modules) are copies of their
versions before the compiler moved to its own copy of the abt library,
so the files here see the same code as before.

`README.md` in this directory is the original overview of the files.
