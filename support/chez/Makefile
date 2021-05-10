include ../../config.mk

all: support-sep.ss

clean:
	$(RM) support-sep.ss

.PHONY: install

install: build
	mkdir -p ${PREFIX}/${NAME_VERSION}/support/chez
	install *.ss ${PREFIX}/${NAME_VERSION}/support/chez

support-sep.ss: support.ss
	# start library header
	echo "(library (support) (export" > $@

	# print the list of exports
	cat support.ss \
		| sed -n 's|(define (\?\([^ )]*\).*|\1|p' \
		>> $@
	echo ") (import chezscheme)" >> $@

	# copy the code
	cat $< >> $@

	# close the bracket
	echo ") ; end of (library)" >> $@
