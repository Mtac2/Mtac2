.PHONY: check all clean
RED='\033[0;31m'
NC='\033[0m' # No Color
COQC=coqc

TESTS=$(wildcard *.v)
RESULTS=$(TESTS:.v=.vo)

all: check

check: $(RESULTS)

%.vo: %.v
	@ ($(COQC) -type-in-type -I ../src -Q ../theories MetaCoq $< && echo "[OK] " $<) || echo "\033[0;31m[KO]\033[0m " $<

clean:
	rm --force $(RESULTS) *.glob .*.aux
