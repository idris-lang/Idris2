all: build
.PHONY: all

build:
	${IDRIS2} --build prelude.ipkg
.PHONY: build

install:
	${IDRIS2} --install prelude.ipkg
.PHONY: install

install-with-src:
	${IDRIS2} --install-with-src prelude.ipkg
.PHONY: install-with-src

docs:
	${IDRIS2} --mkdoc prelude.ipkg
.PHONY: docs

clean:
	$(RM) -r build
.PHONY: clean
