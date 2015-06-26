.PHONY: check all clean

COQC=coqc

TESTS=$(wildcard *.v)
RESULTS=$(TESTS:.v=.vo)

all: check

check: $(RESULTS)

%.vo: %.v
	@ ($(COQC) $< && echo "[OK] " $<) || echo "[KO] " $<

clean:
	rm --force $(RESULTS) *.glob .*.aux
