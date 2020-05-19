INTERACTIVE ?= --interactive

test:
	$(RM) -rf build
	${IDRIS2_BOOT} --build tests.ipkg
	@./build/exec/runtests $(IDRIS2) $(INTERACTIVE) --only $(only)

clean:
	find . -name '*.ibc' | xargs rm -f
	find . -name 'output' | xargs rm -f
