MUNGE = ../src/munge.exe

all: part2.tex

tokens.tex: ../src/tokens.tex
	@cp ../src/tokens.tex .

part2.tex: part2.htex
	$(MUNGE) < part2.htex > part2.tex

clean:
	@rm -f *.aux *.blg *.log [0-9]*.tex *.bbl *.out *.idx *.toc *.ilg *.ind *.hix *.pag *.synctex.gz

dist-clean: clean
	@rm -f *.pdf

.PHONY: all
