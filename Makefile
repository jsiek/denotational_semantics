AGDA ?= agda

# Check the closure-conversion compilers and their correctness proofs
# (agda/All.agda: the FPC compiler of the PLDI 2027 paper, agda/FPC/All.agda,
# but for its Scott-domain column; the ISWIM pipelines, agda/ISWIM/All.agda,
# the preserved untyped one, agda/ISWIM/Untyped/, included; and the
# modules they share, agda/proof/ among them) with --safe, so that nothing
# postulated or unsafe is used, and then check that nothing in the
# checked tree (agda/, but not agda/old/, which is not checked)
# postulates or has a pragma, other than the --without-K of the abt
# extract, and that every line of an Agda file there fits in 80 columns
# (counted in Unicode code points). See agda/README.md.
check: agda pragma-check width-check

agda:
	$(AGDA) --safe agda/All.agda

pragma-check:
	@! grep -rnE --include='*.agda' --exclude-dir=old '\bpostulate\b|\{-#' agda \
	  | grep -vE ':1:\{-# OPTIONS --without-K #-\}$$'

width-check:
	@python3 -c 'import glob, sys; \
	  bad = [f"{f}:{n}: {len(l)} columns" \
	         for f in sorted(glob.glob("agda/**/*.agda", recursive=True)) \
	         if not f.startswith("agda/old/") \
	         for n, l in enumerate(open(f, encoding="utf-8").read().split("\n"), 1) \
	         if len(l) > 80]; \
	  print("\n".join(bad)) if bad else None; sys.exit(1 if bad else 0)'

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

# The anonymized artifact of the PLDI 2027 paper (FPC only), written to
# $(OUT): see artifact/export.py.
OUT ?= _artifact
artifact: scott-deps
	python3 artifact/export.py $(OUT)

.PHONY: check agda pragma-check width-check check-scott scott-deps check-all artifact
