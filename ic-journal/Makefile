MUNGE = ../src/munge.exe
MOPT = -w75

HTEXFILES = part2.tex sos.tex bisim.tex coarsest.tex context.tex \
            conclusions.tex multivariate.tex formal.tex
TEXFILES = main.tex intro.tex ccs.tex expansion.tex multivariate.tex \
           contraction.tex unique.tex equa.tex \
           related.tex tokens.tex $(HTEXFILES)

TEXCMD = pdflatex

all: htex main.pdf main.ps

htex: $(HTEXFILES)

tokens.tex: ../src/tokens.tex
	@cp ../src/tokens.tex .

part2.tex: part2.htex $(MUNGE)
	$(MUNGE) $(MOPT) < part2.htex > part2.tex

formal.tex: formal.htex $(MUNGE)
	$(MUNGE) $(MOPT) < formal.htex > formal.tex

multivariate.tex: multivariate.htex $(MUNGE)
	$(MUNGE) $(MOPT) < multivariate.htex > multivariate.tex

sos.tex: sos.htex $(MUNGE)
	$(MUNGE) $(MOPT) < sos.htex > sos.tex

bisim.tex: bisim.htex $(MUNGE)
	$(MUNGE) $(MOPT) < bisim.htex > bisim.tex

coarsest.tex: coarsest.htex $(MUNGE)
	$(MUNGE) $(MOPT) < coarsest.htex > coarsest.tex

context.tex: context.htex $(MUNGE)
	$(MUNGE) $(MOPT) < context.htex > context.tex

conclusions.tex: conclusions.htex $(MUNGE)
	$(MUNGE) $(MOPT) < conclusions.htex > conclusions.tex

clean:
	@rm -f *.aux *.blg *.log [0-9]*.tex *.out *.idx *.toc *.ilg *.ind *.hix *.pag \
               *.synctex.gz Thumbs.db *.spl

distclean: clean
	@rm -f *.pdf *.dvi *.ps

main.pdf: $(TEXFILES) generic.bib
	$(TEXCMD) main
	$(TEXCMD) main
	bibtex main
	$(TEXCMD) main
	$(TEXCMD) main

main.dvi: $(TEXFILES) generic.bib
	latex main
	latex main
	bibtex main
	latex main
	latex main

main.ps: main.dvi
	dvips main

force: htex
	bibtex main
	$(TEXCMD) main

quick: htex
	$(TEXCMD) main

.PHONY: all
