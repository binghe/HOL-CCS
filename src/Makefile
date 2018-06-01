REL_FILES = Holmakefile CCSScript.sml *Lib.sig *Lib.sml *Conv.sig *Conv.sml tokens.tex \
	CCSSyntax.sml CCSSyntax.sig selftest.sml \
	StrongEQScript.sml StrongLawsScript.sml \
	WeakEQScript.sml WeakLawsScript.sml \
	ObsCongrScript.sml ObsCongrLawsScript.sml \
	CoarsestCongrScript.sml ExampleScript.sml \
	CongruenceScript.sml TraceScript.sml \
	ExpansionScript.sml ContractionScript.sml \
	BisimulationUptoScript.sml UniqueSolutionsScript.sml

INFORMATICA_PUBLIC = ../../../../Informatica-public

all:
	Holmake

clean:
	Holmake clean
	@rm -rf .HOLMK .hollogs

release:
	@mkdir -p $(INFORMATICA_PUBLIC)/thesis/src
	@cp -f $(REL_FILES) $(INFORMATICA_PUBLIC)/thesis/src

.PHONY: all
