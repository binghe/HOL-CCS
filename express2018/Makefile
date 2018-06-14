MUNGE = ../src/munge.exe
TEXFILES = main.tex part2.tex intro.tex bisim.tex sos.tex ccs.tex expansion.tex \
	contraction.tex unique.tex equa.tex formal.tex coarsest.tex context.tex \
	related.tex conclusions.tex tokens.tex

all: htex main.pdf

htex: $(MUNGE) part2.tex sos.tex bisim.tex coarsest.tex context.tex

tokens.tex: ../src/tokens.tex
	@cp ../src/tokens.tex .

part2.tex: part2.htex
	$(MUNGE) < part2.htex > part2.tex

sos.tex: sos.htex
	$(MUNGE) < sos.htex > sos.tex

bisim.tex: bisim.htex
	$(MUNGE) < bisim.htex > bisim.tex

coarsest.tex: coarsest.htex
	$(MUNGE) < coarsest.htex > coarsest.tex

context.tex: context.htex
	$(MUNGE) < context.htex > context.tex

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
