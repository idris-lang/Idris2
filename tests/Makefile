INTERACTIVE ?= --interactive

.PHONY: testbin test

test:
	./build/exec/runtests $(IDRIS2) $(INTERACTIVE) --only $(only)

testbin: build/exec/runtests

build/exec/runtests:
	${IDRIS2_BOOT} --build tests.ipkg

clean:
	$(RM) -r build
	@find . -type f -name 'output' -exec rm -rf {} \;
	@find . -type f -name '*.ttc' -exec rm -f {} \;
	@find . -type f -name '*.ttm' -exec rm -f {} \;
	@find . -type f -name '*.ibc' -exec rm -f {} \;
