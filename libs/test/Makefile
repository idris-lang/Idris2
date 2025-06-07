all: build
.PHONY: all

build:
	${IDRIS2} --build test.ipkg
.PHONY: build

install:
	${IDRIS2} --install test.ipkg
.PHONY: install

install-with-src:
	${IDRIS2} --install-with-src test.ipkg
.PHONY: install-with-src

docs:
	${IDRIS2} --mkdoc test.ipkg
.PHONY: docs

clean:
	$(RM) -r build
.PHONY: clean
