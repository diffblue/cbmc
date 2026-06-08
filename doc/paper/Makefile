.PHONY: all clean

all: paper.pdf

paper.pdf: paper.tex references.bib
	-pdflatex -interaction=nonstopmode paper.tex
	-bibtex paper
	-pdflatex -interaction=nonstopmode paper.tex
	-pdflatex -interaction=nonstopmode paper.tex
	@grep -q "Output written" paper.log && echo "Build successful." || echo "Build FAILED."
	@grep "Warning.*Citation.*undefined\|Warning.*Reference.*undefined" paper.log | head -3; true

clean:
	rm -f paper.pdf paper.aux paper.bbl paper.blg paper.log paper.out paper.toc
