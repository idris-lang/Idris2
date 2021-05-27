INTERACTIVE ?= --interactive
threads ?= $(shell (nproc || sysctl -n hw.ncpu) 2>/dev/null || echo 1)

.PHONY: testbin test

test:
	./build/exec/runtests $(IDRIS2) $(INTERACTIVE) --failure-file failures --threads $(threads) --only $(only)

retest:
	./build/exec/runtests $(IDRIS2) $(INTERACTIVE) --failure-file failures --threads $(threads) --only-file failures --only $(only)

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
