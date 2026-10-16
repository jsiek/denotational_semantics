## Build the paper with the acmart class in acmart-primary/.
export TEXINPUTS := ./acmart-primary//:$(TEXINPUTS)

paper.pdf: paper.tex intro.tex delay.tex contributions.tex abstract.tex all.bib
	pdflatex -interaction=nonstopmode paper.tex
	bibtex paper
	pdflatex -interaction=nonstopmode paper.tex
	pdflatex -interaction=nonstopmode paper.tex

clean:
	rm -f paper.pdf paper.bbl paper.blg paper.aux paper.log paper.out paper.fls paper.fdb_latexmk

.PHONY: clean
