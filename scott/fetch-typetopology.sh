#!/bin/sh
# Fetch the TypeTopology library (Martin Escardo et al.; the domain theory
# is Tom de Jong's), at a pinned commit, into _deps/TypeTopology (git
# ignored), apply scott/typetopology-builtin-alias.patch, and write the
# libraries file _deps/libraries: the default libraries file of this
# Agda (so the standard library is found as for `make check`) plus
# TypeTopology.  Used by `make check-scott`; see agda/Framework/Scott/.
#
# The patch makes TypeTopology's ℕ, Bool and List the builtin ones of
# Agda.Builtin.* (as the standard library's are) and drops its NATPLUS
# and NATTIMES pragmas, so that a module may import both libraries.
set -eu

ROOT=$(cd "$(dirname "$0")/.." && pwd)
DEPS="$ROOT/_deps"
TT="$DEPS/TypeTopology"
COMMIT=17487fc910f3bb305c30001507fed5d41d52dc3c
URL=https://github.com/martinescardo/TypeTopology.git
AGDA=${AGDA:-agda}

if [ ! -f "$TT/.fetched-$COMMIT" ]; then
  rm -rf "$TT"
  mkdir -p "$TT"
  git -C "$TT" init -q
  git -C "$TT" remote add origin "$URL"
  git -C "$TT" fetch -q --depth 1 origin "$COMMIT"
  git -C "$TT" checkout -q FETCH_HEAD
  git -C "$TT" apply "$ROOT/scott/typetopology-builtin-alias.patch"
  touch "$TT/.fetched-$COMMIT"
fi

APPDIR=$($AGDA --print-agda-app-dir)
VERSION=$($AGDA --numeric-version)
{
  if [ -f "$APPDIR/libraries-$VERSION" ]; then
    cat "$APPDIR/libraries-$VERSION"
  elif [ -f "$APPDIR/libraries" ]; then
    cat "$APPDIR/libraries"
  fi
  echo "$TT/typetopology.agda-lib"
} > "$DEPS/libraries"
