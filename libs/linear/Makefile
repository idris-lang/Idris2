all: build
.PHONY: all

build:
	${IDRIS2} --build linear.ipkg
.PHONY: build

install:
	${IDRIS2} --install linear.ipkg
.PHONY: install

install-with-src:
	${IDRIS2} --install-with-src linear.ipkg
.PHONY: install-with-src

docs:
	${IDRIS2} --mkdoc linear.ipkg
.PHONY: docs

clean:
	$(RM) -r build
.PHONY: clean
