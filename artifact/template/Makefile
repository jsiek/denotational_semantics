AGDA ?= agda
PYTHON ?= python3

# Check the graph model, abstract machines, clocked interpreters, reduction
# semantics and adequacy (agda/Mu/All.agda) with --safe, using only the
# standard library; then check that no checked file postulates or has a
# pragma (other than the --without-K of the abt extract).
check: agda pragma-check

agda:
	$(AGDA) --safe agda/Mu/All.agda

pragma-check:
	@! grep -rnE --include='*.agda' '\bpostulate\b|\{-#' agda \
	  | grep -vE ':1:\{-# OPTIONS --without-K #-\}$$'
	@echo 'pragma-check: no postulates, no pragmas'

# The Scott-domain proofs (agda/AllScott.agda), with --safe, using the
# standard library and the TypeTopology vendored in vendor/TypeTopology/.
# _build/libraries is the default libraries file of this Agda (so that the
# standard library is found as for `make check`) plus TypeTopology's.
check-scott: libraries
	$(AGDA) --library-file=_build/libraries -l standard-library -l TypeTopology \
	  -i agda --safe agda/AllScott.agda
	@$(MAKE) --no-print-directory pragma-check

libraries:
	@mkdir -p _build
	@APPDIR=$$($(AGDA) --print-agda-app-dir); VERSION=$$($(AGDA) --numeric-version); \
	{ if [ -f "$$APPDIR/libraries-$$VERSION" ]; then cat "$$APPDIR/libraries-$$VERSION"; \
	  elif [ -f "$$APPDIR/libraries" ]; then cat "$$APPDIR/libraries"; fi; \
	  echo "$(CURDIR)/vendor/TypeTopology/typetopology.agda-lib"; } > _build/libraries

# Tables 1 and 2 of the paper (lines of code; needs only Python 3)
tables:
	$(PYTHON) loc.py --artifact

all: check check-scott tables

# remove Agda's interface files
clean:
	rm -rf _build vendor/TypeTopology/_build
	find . -name '*.agdai' -delete

.PHONY: check agda pragma-check check-scott libraries tables all clean
