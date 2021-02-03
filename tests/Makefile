INTERACTIVE ?= --interactive

.PHONY: testbin test

test: check
	./build/exec/runtests $(IDRIS2) $(INTERACTIVE) --only $(only)

check:
	if [ ! -x "${IDRIS2}" ]; then echo "\nERROR: Missing IDRIS2 executable. Cannot run tests!\n"; exit 1; fi

testbin:
	${IDRIS2_BOOT} --build tests.ipkg

clean:
	$(RM) -r build
	@find . -type f -name 'output' -exec rm -rf {} \;
	@find . -type f -name '*.ttc' -exec rm -f {} \;
	@find . -type f -name '*.ttm' -exec rm -f {} \;
	@find . -type f -name '*.ibc' -exec rm -f {} \;
