SRC = $(shell find . -type f -name '*.v')
OBJ = $(SRC:.v=.vo)

TIME = time -p
COQC = coqc
COQFLAGS = -noglob

COUNT_PROOF = $(shell grep -c "Proof." $(SRC) | awk -F ':' '{total += $$2} END { print total }')
COUNT_MPROOF = $(shell grep -c "MProof." $(SRC) | awk -F ':' '{total += $$2} END { print total }')

all:
	@$(TIME) $(MAKE) --silent bench
	@echo -n "MProoved: "
	@echo 'x = ($(COUNT_MPROOF) / $(COUNT_PROOF)) * 100\nprint x, "%\n"' | bc -l

clean:
	@$(RM) $(OBJ)

bench: $(OBJ)

%.vo: %.v
	$(COQC) $(COQFLAGS) $<

.PHONY: all clean bench
