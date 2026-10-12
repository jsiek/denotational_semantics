#!/bin/sh
# Check Agda files of the Scott-domain column, with the standard library
# and TypeTopology (run scott/fetch-typetopology.sh first; `make
# check-scott` does both).
set -eu
ROOT=$(cd "$(dirname "$0")/.." && pwd)
cd "$ROOT"
exec ${AGDA:-agda} --library-file=_deps/libraries -l standard-library \
  -l TypeTopology -i agda --safe "$@"
