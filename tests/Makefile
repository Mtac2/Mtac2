.PHONY: check all clean
RED='\033[0;31m'
NC='\033[0m' # No Color
COQC=coqc

TESTS=$(wildcard *.v)
RESULTS=$(TESTS:.v=.vo)

all: check

check: $(RESULTS)

%.vo: %.v
	@ ($(COQC) -I ../src -Q ../theories Mtac2 $< && echo "[OK] " $<) || ( EXITSTATE="$$?"; echo "\033[0;31m[KO]\033[0m" $<; exit "$$EXITSTATE" )

clean:
	rm --force $(RESULTS) *.glob .*.aux
