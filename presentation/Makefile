MUNGE = ../src/munge.exe

# XeTeX results into much smaller PDF
TEXCMD = pdflatex

all: express2018.pdf

htex: express2018-body.tex

tokens.tex: ../src/tokens.tex
	@cp ../src/tokens.tex .

express2018-body.tex: express2018-body.htex
	$(MUNGE) < express2018-body.htex > express2018-body.tex

express2018.pdf: express2018.tex express2018-body.tex tokens.tex $(MUNGE)
	pdflatex express2018
	pdflatex express2018

clean:
	@rm -f *.aux *.blg *.log [0-9]*.tex *.bbl *.out *.idx *.toc *.ilg *.ind *.hix *.pag *.synctex.gz

dist-clean: clean
	@rm -f *.pdf

.PHONY: all
