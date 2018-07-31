MUNGE = ../src/munge.exe

# XeTeX results into much smaller PDF
TEXCMD = pdflatex

all: tokens.tex

tokens.tex: ../src/tokens.tex
	@cp ../src/tokens.tex .

clean:
	@rm -f *.aux *.blg *.log [0-9]*.tex *.bbl *.out *.idx *.toc *.ilg *.ind *.hix *.pag *.synctex.gz

dist-clean: clean
	@rm -f *.pdf

.PHONY: all
