all: build
.PHONY: all

build:
	${IDRIS2} --build base.ipkg
.PHONY: build

install:
	${IDRIS2} --install base.ipkg
.PHONY: install

install-with-src:
	${IDRIS2} --install-with-src base.ipkg
.PHONY: install-with-src

docs:
	${IDRIS2} --mkdoc base.ipkg
.PHONY: docs

clean:
	$(RM) -r build
.PHONY: clean
