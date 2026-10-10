AGDA ?= agda

# Check the closure-conversion compiler and its correctness proofs
# (agda/All.agda), with --safe so that nothing postulated is used.
check:
	$(AGDA) --safe agda/All.agda

.PHONY: check
