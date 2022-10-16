INTERACTIVE ?= --interactive
threads ?= $(shell (nproc || sysctl -n hw.ncpu) 2>/dev/null || echo 1)

.PHONY: testbin test

ifneq ($(only),)
ONLYOPT := --only $(only)
endif

test:
	./build/exec/runtests $(IDRIS2) $(INTERACTIVE) --timing --failure-file failures --threads $(threads) $(ONLYOPT)

retest:
	./build/exec/runtests $(IDRIS2) $(INTERACTIVE) --timing --failure-file failures --threads $(threads) --only-file failures $(ONLYOPT)

testbin:
	${IDRIS2} --build tests.ipkg

clean:
	$(RM) failures
	$(RM) -r build
	$(RM) -r **/**/build
	@find . -type f -name 'output' -exec rm -rf {} \;
	@find . -type f -name '*.ttc' -exec rm -f {} \;
	@find . -type f -name '*.ttm' -exec rm -f {} \;
	@find . -type f -name '*.ibc' -exec rm -f {} \;
