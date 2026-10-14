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

.PHONY: check agda pragma-check
