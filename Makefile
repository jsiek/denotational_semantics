AGDA ?= agda

# Check the closure-conversion compiler and its correctness proofs
# (agda/All.agda: the theorem statements in agda/Theorems and everything
# in agda/proof) with --safe, so that nothing postulated or unsafe is
# used, and then check that nothing in the checked tree (agda/, but not
# agda/old/, which is not checked) postulates or has a pragma, other than
# the --without-K of the abt extract. See agda/README.md.
check: agda pragma-check

agda:
	$(AGDA) --safe agda/All.agda

pragma-check:
	@! grep -rnE --include='*.agda' --exclude-dir=old '\bpostulate\b|\{-#' agda \
	  | grep -vE ':1:\{-# OPTIONS --without-K #-\}$$'

.PHONY: check agda pragma-check
