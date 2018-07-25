MUNGE = ../src/munge.exe

HTEXFILES = part2.tex sos.tex bisim.tex coarsest.tex context.tex conclusions.tex
TEXFILES = main.tex intro.tex ccs.tex expansion.tex \
	contraction.tex unique.tex equa.tex formal.tex \
	related.tex conclusions.tex tokens.tex $(HTEXFILES)

# XeTeX results into much smaller PDF
TEXCMD = pdflatex

all: htex main.pdf main.ps

htex: $(HTEXFILES)

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

conclusions.tex: conclusions.htex
	$(MUNGE) < conclusions.htex > conclusions.tex

clean:
	@rm -f *.aux *.blg *.log [0-9]*.tex *.bbl *.out *.idx *.toc *.ilg *.ind *.hix *.pag *.synctex.gz

dist-clean: clean
	@rm -f *.pdf

main.pdf: $(TEXFILES) generic.bib
	$(TEXCMD) main
	$(TEXCMD) main
	bibtex main
	$(TEXCMD) main
	$(TEXCMD) main

main.ps: main.pdf
	latex main
	dvips main

force: htex
	bibtex main
	$(TEXCMD) main

.PHONY: all
