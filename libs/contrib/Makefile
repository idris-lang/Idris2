all: build
.PHONY: all

build:
	${IDRIS2} --build contrib.ipkg
.PHONY: build

install:
	${IDRIS2} --install contrib.ipkg
.PHONY: install

install-with-src:
	${IDRIS2} --install-with-src contrib.ipkg
.PHONY: install-with-src

docs:
	${IDRIS2} --mkdoc contrib.ipkg
.PHONY: docs

clean:
	$(RM) -r build
.PHONY: clean
