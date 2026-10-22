AGDA ?= agda

# Check the closure-conversion compiler and its correctness proofs
# (agda/All.agda: the theorem statements in agda/Theorems, everything in
# agda/proof, and the preserved untyped pipeline, agda/Untyped/All.agda)
# with --safe, so that nothing postulated or unsafe is used, and then
# check that nothing in the checked tree (agda/, agda/Untyped/ included,
# but not agda/old/, which is not checked) postulates or has a pragma,
# other than the --without-K of the abt extract. See agda/README.md.
check: agda pragma-check

agda:
	$(AGDA) --safe agda/All.agda

pragma-check:
	@! grep -rnE --include='*.agda' --exclude-dir=old '\bpostulate\b|\{-#' agda \
	  | grep -vE ':1:\{-# OPTIONS --without-K #-\}$$'

# The denotational: Scott domains column (agda/AllScott.agda) needs, besides
# the standard library, TypeTopology (for Tom de Jong's domain theory):
# scott/fetch-typetopology.sh clones it at a pinned commit into _deps/
# (git ignored), patches it, and writes the libraries file _deps/libraries;
# scott/check.sh checks with it. `make check` does not need TypeTopology.
check-scott: scott-deps
	AGDA=$(AGDA) ./scott/check.sh agda/AllScott.agda
	@$(MAKE) --no-print-directory pragma-check

scott-deps:
	AGDA=$(AGDA) ./scott/fetch-typetopology.sh

check-all: check check-scott

.PHONY: check agda pragma-check check-scott scott-deps check-all
