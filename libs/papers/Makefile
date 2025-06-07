all: build
.PHONY: all

build:
	${IDRIS2} --build papers.ipkg
.PHONY: build

install:
	${IDRIS2} --install papers.ipkg
.PHONY: install

install-with-src:
	${IDRIS2} --install-with-src papers.ipkg
.PHONY: install-with-src

docs:
	${IDRIS2} --mkdoc papers.ipkg
.PHONY: docs

clean:
	$(RM) -r build
.PHONY: clean
