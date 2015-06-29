.PHONY: check cleanall

-include Makefile

# The workflow is:
# 1. Develop in src
# 2. Once it compiles and seems correct, use the test-suite
#    before committing by doing `make check`.

check:
	@ $(MAKE) --silent all install
	@ $(MAKE) --silent -C tests clean check

cleanall:
	@ $(MAKE) --silent clean
	@ $(MAKE) --silent -C tests clean
