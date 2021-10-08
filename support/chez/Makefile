include ../../common.mk

all: build

clean:
	-$(RM) support-sep.ss

.PHONY: install  build

build: support-sep.ss

install: build
	mkdir -p "$(PREFIX)/$(IDRIS_INSTALL_DIR)/support/chez"
	install -m 644 *.ss "$(PREFIX)/$(IDRIS_INSTALL_DIR)/support/chez"

support-sep.ss: support.ss
	# start library header
	echo "(library (support) (export" > $@

	# print the list of exports
	cat support.ss \
		| sed -n 's|(define (\?\([^ )]*\).*|\1|p' \
		>> $@
	echo ") (import (chezscheme))" >> $@

	# copy the code
	cat $< >> $@

	# close the bracket
	echo ") ; end of (library)" >> $@
