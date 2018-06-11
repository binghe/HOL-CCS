MUNGE = ../src/munge.exe
TEXFILES = main.tex part2.tex intro.tex ccs.tex expansion.tex contraction.tex unique.tex

all: main.pdf

tokens.tex: ../src/tokens.tex
	@cp ../src/tokens.tex .

part2.tex: part2.htex
	$(MUNGE) < part2.htex > part2.tex

clean:
	@rm -f *.aux *.blg *.log [0-9]*.tex *.bbl *.out *.idx *.toc *.ilg *.ind *.hix *.pag *.synctex.gz

dist-clean: clean
	@rm -f *.pdf

main.pdf: $(TEXFILES) generic.bib
	pdflatex main
	pdflatex main
	bibtex main
	pdflatex main
	pdflatex main

.PHONY: all
