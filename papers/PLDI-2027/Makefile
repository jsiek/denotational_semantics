## Build the paper with the acmart class in acmart-primary/.
export TEXINPUTS := ./acmart-primary//:$(TEXINPUTS)

paper.pdf: paper.tex
	pdflatex -interaction=nonstopmode paper.tex
	pdflatex -interaction=nonstopmode paper.tex

clean:
	rm -f paper.pdf paper.aux paper.log paper.out paper.fls paper.fdb_latexmk

.PHONY: clean
