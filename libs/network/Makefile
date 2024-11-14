all: build
.PHONY: all

build:
	${IDRIS2} --build network.ipkg
.PHONY: build

install:
	${IDRIS2} --install network.ipkg
.PHONY: install

install-with-src:
	${IDRIS2} --install-with-src network.ipkg
.PHONY: install-with-src

docs:
	${IDRIS2} --mkdoc network.ipkg
.PHONY: docs

clean:
	$(RM) -r build
.PHONY: clean

