include config.mk

# Idris 2 executable used to bootstrap
export IDRIS2_BOOT ?= idris2

# Idris 2 executable we're building
NAME = idris2
TARGETDIR = ${CURDIR}/build/exec
TARGET = ${TARGETDIR}/${NAME}

# Default code generator. This is passed to the libraries for incremental
# builds, but overridable via environment variables or arguments to make
IDRIS2_CG ?= chez

MAJOR=0
MINOR=6
PATCH=0

GIT_SHA1=
ifeq ($(shell git status >/dev/null 2>&1; echo $$?), 0)
	# inside a git repo
	ifneq ($(shell git describe --exact-match --tags >/dev/null 2>&1; echo $$?), 0)
		# not tagged as a released version, so add sha1 of this build in between releases
		GIT_SHA1 := $(shell git rev-parse --short=9 HEAD)
	endif
endif
VERSION_TAG ?= $(GIT_SHA1)

export IDRIS2_VERSION := ${MAJOR}.${MINOR}.${PATCH}
export NAME_VERSION := ${NAME}-${IDRIS2_VERSION}
IDRIS2_SUPPORT := libidris2_support${SHLIB_SUFFIX}
IDRIS2_APP_IPKG := idris2.ipkg
IDRIS2_LIB_IPKG := idris2api.ipkg

ifeq ($(OS), windows)
	# This produces D:/../.. style paths
	IDRIS2_PREFIX := $(shell cygpath -m ${PREFIX})
	IDRIS2_CURDIR := $(shell cygpath -m ${CURDIR})
	SEP := ;
else
	IDRIS2_PREFIX := ${PREFIX}
	IDRIS2_CURDIR := ${CURDIR}
	SEP := :
endif

TEST_PREFIX ?= ${IDRIS2_CURDIR}/build/env

# Library and data paths for bootstrap-test
IDRIS2_BOOT_PREFIX := ${IDRIS2_CURDIR}/bootstrap-build

# These are the library path in the build dir to be used during build
IDRIS2_LIBRARIES = prelude base linear network contrib test

IDRIS2_BOOT_PATH =
$(foreach library,$(IDRIS2_LIBRARIES),$(eval IDRIS2_BOOT_PATH := $(IDRIS2_BOOT_PATH)$(IDRIS2_CURDIR)/libs/$(library)/build/ttc$(SEP)))
export IDRIS2_BOOT_PATH := "$(IDRIS2_BOOT_PATH)"

export SCHEME

.PHONY: all idris2-exec libdocs testenv testenv-clean support clean-support clean FORCE

all: support ${TARGET} libs

idris2-exec: ${TARGET}

${TARGET}: src/IdrisPaths.idr
	${IDRIS2_BOOT} --build ${IDRIS2_APP_IPKG}

# We use FORCE to always rebuild IdrisPath so that the git SHA1 info is always up to date
src/IdrisPaths.idr: FORCE
	echo "-- @""generated" > src/IdrisPaths.idr
	echo 'module IdrisPaths' >> src/IdrisPaths.idr
	echo 'export idrisVersion : ((Nat,Nat,Nat), String); idrisVersion = ((${MAJOR},${MINOR},${PATCH}), "${VERSION_TAG}")' >> src/IdrisPaths.idr
	echo 'export yprefix : String; yprefix="${IDRIS2_PREFIX}"' >> src/IdrisPaths.idr

FORCE:

prelude:
	${MAKE} -C libs/prelude IDRIS2=${TARGET} IDRIS2_INC_CGS=${IDRIS2_CG} IDRIS2_PATH=${IDRIS2_BOOT_PATH}

base: prelude
	${MAKE} -C libs/base IDRIS2=${TARGET} IDRIS2_INC_CGS=${IDRIS2_CG} IDRIS2_PATH=${IDRIS2_BOOT_PATH}

network: prelude linear
	${MAKE} -C libs/network IDRIS2=${TARGET} IDRIS2_INC_CGS=${IDRIS2_CG} IDRIS2_PATH=${IDRIS2_BOOT_PATH}

contrib: base
	${MAKE} -C libs/contrib IDRIS2=${TARGET} IDRIS2_INC_CGS=${IDRIS2_CG} IDRIS2_PATH=${IDRIS2_BOOT_PATH}

test-lib: contrib
	${MAKE} -C libs/test IDRIS2=${TARGET} IDRIS2_INC_CGS=${IDRIS2_CG} IDRIS2_PATH=${IDRIS2_BOOT_PATH}

linear: prelude
	${MAKE} -C libs/linear IDRIS2=${TARGET} IDRIS2_INC_CGS=${IDRIS2_CG} IDRIS2_PATH=${IDRIS2_BOOT_PATH}

papers: contrib linear
	${MAKE} -C libs/papers IDRIS2=${TARGET} IDRIS2_INC_CGS=${IDRIS2_CG} IDRIS2_PATH=${IDRIS2_BOOT_PATH}

bootstrap-libs : prelude base linear network
libs : prelude base contrib network test-lib linear papers

libdocs:
	${MAKE} -C libs/prelude docs IDRIS2=${TARGET} IDRIS2_PATH=${IDRIS2_BOOT_PATH}
	${MAKE} -C libs/base docs IDRIS2=${TARGET} IDRIS2_PATH=${IDRIS2_BOOT_PATH}
	${MAKE} -C libs/contrib docs IDRIS2=${TARGET} IDRIS2_PATH=${IDRIS2_BOOT_PATH}
	${MAKE} -C libs/network docs IDRIS2=${TARGET} IDRIS2_PATH=${IDRIS2_BOOT_PATH}
	${MAKE} -C libs/test docs IDRIS2=${TARGET} IDRIS2_PATH=${IDRIS2_BOOT_PATH}
	${MAKE} -C libs/linear docs IDRIS2=${TARGET} IDRIS2_PATH=${IDRIS2_BOOT_PATH}


ifeq ($(OS), windows)
${TEST_PREFIX}/${NAME_VERSION} :
	${MAKE} install-support PREFIX=${TEST_PREFIX}
	cp -rf ${IDRIS2_CURDIR}/libs/prelude/build/ttc ${TEST_PREFIX}/${NAME_VERSION}/prelude-${IDRIS2_VERSION}
	cp -rf ${IDRIS2_CURDIR}/libs/base/build/ttc    ${TEST_PREFIX}/${NAME_VERSION}/base-${IDRIS2_VERSION}
	cp -rf ${IDRIS2_CURDIR}/libs/linear/build/ttc  ${TEST_PREFIX}/${NAME_VERSION}/linear-${IDRIS2_VERSION}
	cp -rf ${IDRIS2_CURDIR}/libs/network/build/ttc ${TEST_PREFIX}/${NAME_VERSION}/network-${IDRIS2_VERSION}
	cp -rf ${IDRIS2_CURDIR}/libs/contrib/build/ttc ${TEST_PREFIX}/${NAME_VERSION}/contrib-${IDRIS2_VERSION}
	cp -rf ${IDRIS2_CURDIR}/libs/test/build/ttc    ${TEST_PREFIX}/${NAME_VERSION}/test-${IDRIS2_VERSION}
else
${TEST_PREFIX}/${NAME_VERSION} :
	${MAKE} install-support PREFIX=${TEST_PREFIX}
	ln -sf ${IDRIS2_CURDIR}/libs/prelude/build/ttc ${TEST_PREFIX}/${NAME_VERSION}/prelude-${IDRIS2_VERSION}
	ln -sf ${IDRIS2_CURDIR}/libs/base/build/ttc    ${TEST_PREFIX}/${NAME_VERSION}/base-${IDRIS2_VERSION}
	ln -sf ${IDRIS2_CURDIR}/libs/linear/build/ttc  ${TEST_PREFIX}/${NAME_VERSION}/linear-${IDRIS2_VERSION}
	ln -sf ${IDRIS2_CURDIR}/libs/network/build/ttc ${TEST_PREFIX}/${NAME_VERSION}/network-${IDRIS2_VERSION}
	ln -sf ${IDRIS2_CURDIR}/libs/contrib/build/ttc ${TEST_PREFIX}/${NAME_VERSION}/contrib-${IDRIS2_VERSION}
	ln -sf ${IDRIS2_CURDIR}/libs/test/build/ttc    ${TEST_PREFIX}/${NAME_VERSION}/test-${IDRIS2_VERSION}
endif

.PHONY: ${TEST_PREFIX}/${NAME_VERSION}

testenv:
	@${MAKE} ${TEST_PREFIX}/${NAME_VERSION}
	@${MAKE} -C tests testbin IDRIS2=${TARGET} IDRIS2_PREFIX=${TEST_PREFIX}

testenv-clean:
	$(RM) -r ${TEST_PREFIX}/${NAME_VERSION}

ci-ubuntu-test: test
ci-macos-test: test
ci-windows-test:
	@${MAKE} test except="idris2/repl005"

test: testenv
	@echo
	@echo "NOTE: \`${MAKE} test\` does not rebuild Idris or the libraries packaged with it; to do that run \`${MAKE}\`"
	@if [ ! -x "${TARGET}" ]; then echo "ERROR: Missing IDRIS2 executable. Cannot run tests!\n"; exit 1; fi
	@echo
	@${MAKE} -C tests only=$(only) except=$(except) IDRIS2=${TARGET} IDRIS2_PREFIX=${TEST_PREFIX}


retest: testenv
	@echo
	@echo "NOTE: \`${MAKE} retest\` does not rebuild Idris or the libraries packaged with it; to do that run \`${MAKE}\`"
	@if [ ! -x "${TARGET}" ]; then echo "ERROR: Missing IDRIS2 executable. Cannot run tests!\n"; exit 1; fi
	@echo
	@${MAKE} -C tests retest only=$(only) IDRIS2=${TARGET} IDRIS2_PREFIX=${TEST_PREFIX}

test-installed:
	@${MAKE} -C tests testbin      IDRIS2=$(IDRIS2_PREFIX)/bin/idris2 IDRIS2_PREFIX=${IDRIS2_PREFIX}
	@${MAKE} -C tests only=$(only) IDRIS2=$(IDRIS2_PREFIX)/bin/idris2 IDRIS2_PREFIX=${IDRIS2_PREFIX}

support:
	@${MAKE} -C support

clean-support:
	@${MAKE} -C support clean

clean-libs:
	${MAKE} -C libs/prelude clean
	${MAKE} -C libs/base clean
	${MAKE} -C libs/contrib clean
	${MAKE} -C libs/network clean
	${MAKE} -C libs/test clean
	${MAKE} -C libs/linear clean
	${MAKE} -C libs/papers clean

clean: clean-libs clean-support testenv-clean
	-${IDRIS2_BOOT} --clean ${IDRIS2_APP_IPKG}
	$(RM) src/IdrisPaths.idr
	${MAKE} -C tests clean
	$(RM) -r build

install: install-idris2 install-support install-libs
bootstrap-install: install-idris2 install-support install-bootstrap-libs

install-api: src/IdrisPaths.idr
	${IDRIS2_BOOT} --install ${IDRIS2_LIB_IPKG}

install-with-src-api: src/IdrisPaths.idr
	${IDRIS2_BOOT} --install-with-src ${IDRIS2_LIB_IPKG}

install-idris2:
	mkdir -p ${PREFIX}/bin/
	install ${TARGET} ${PREFIX}/bin
ifeq ($(OS), windows)
	-install ${TARGET}.cmd ${PREFIX}/bin
endif
	mkdir -p ${PREFIX}/bin/${NAME}_app
	install ${TARGETDIR}/${NAME}_app/* ${PREFIX}/bin/${NAME}_app

install-support:
	@${MAKE} -C support install

install-bootstrap-libs:
	${MAKE} -C libs/prelude install IDRIS2=${TARGET} IDRIS2_PATH=${IDRIS2_BOOT_PATH} IDRIS2_INC_CGS=${IDRIS2_CG}
	${MAKE} -C libs/base install    IDRIS2=${TARGET} IDRIS2_PATH=${IDRIS2_BOOT_PATH} IDRIS2_INC_CGS=${IDRIS2_CG}
	${MAKE} -C libs/linear install  IDRIS2=${TARGET} IDRIS2_PATH=${IDRIS2_BOOT_PATH} IDRIS2_INC_CGS=${IDRIS2_CG}
	${MAKE} -C libs/network install IDRIS2=${TARGET} IDRIS2_PATH=${IDRIS2_BOOT_PATH} IDRIS2_INC_CGS=${IDRIS2_CG}

install-libs: install-bootstrap-libs
	${MAKE} -C libs/contrib install IDRIS2=${TARGET} IDRIS2_PATH=${IDRIS2_BOOT_PATH} IDRIS2_INC_CGS=${IDRIS2_CG}
	${MAKE} -C libs/test install IDRIS2=${TARGET} IDRIS2_PATH=${IDRIS2_BOOT_PATH} IDRIS2_INC_CGS=${IDRIS2_CG}

install-with-src-libs:
	${MAKE} -C libs/prelude install-with-src IDRIS2=${TARGET} IDRIS2_PATH=${IDRIS2_BOOT_PATH} IDRIS2_INC_CGS=${IDRIS2_CG}
	${MAKE} -C libs/base install-with-src    IDRIS2=${TARGET} IDRIS2_PATH=${IDRIS2_BOOT_PATH} IDRIS2_INC_CGS=${IDRIS2_CG}
	${MAKE} -C libs/contrib install-with-src IDRIS2=${TARGET} IDRIS2_PATH=${IDRIS2_BOOT_PATH} IDRIS2_INC_CGS=${IDRIS2_CG}
	${MAKE} -C libs/network install-with-src IDRIS2=${TARGET} IDRIS2_PATH=${IDRIS2_BOOT_PATH} IDRIS2_INC_CGS=${IDRIS2_CG}
	${MAKE} -C libs/test install-with-src    IDRIS2=${TARGET} IDRIS2_PATH=${IDRIS2_BOOT_PATH} IDRIS2_INC_CGS=${IDRIS2_CG}
	${MAKE} -C libs/linear install-with-src  IDRIS2=${TARGET} IDRIS2_PATH=${IDRIS2_BOOT_PATH} IDRIS2_INC_CGS=${IDRIS2_CG}

install-libdocs: libdocs
	mkdir -p ${PREFIX}/${NAME_VERSION}/docs/prelude
	mkdir -p ${PREFIX}/${NAME_VERSION}/docs/base
	mkdir -p ${PREFIX}/${NAME_VERSION}/docs/contrib
	mkdir -p ${PREFIX}/${NAME_VERSION}/docs/network
	mkdir -p ${PREFIX}/${NAME_VERSION}/docs/test
	mkdir -p ${PREFIX}/${NAME_VERSION}/docs/linear
	cp -r libs/prelude/build/docs/* ${PREFIX}/${NAME_VERSION}/docs/prelude
	cp -r libs/base/build/docs/*    ${PREFIX}/${NAME_VERSION}/docs/base
	cp -r libs/contrib/build/docs/* ${PREFIX}/${NAME_VERSION}/docs/contrib
	cp -r libs/network/build/docs/* ${PREFIX}/${NAME_VERSION}/docs/network
	cp -r libs/test/build/docs/*    ${PREFIX}/${NAME_VERSION}/docs/test
	cp -r libs/linear/build/docs/*  ${PREFIX}/${NAME_VERSION}/docs/linear
	install -m 644 support/docs/*   ${PREFIX}/${NAME_VERSION}/docs


.PHONY: bootstrap bootstrap-build bootstrap-racket bootstrap-racket-build bootstrap-test bootstrap-clean

# Bootstrapping using SCHEME
bootstrap: support
	@if [ "$$(echo '(threaded?)' | $(SCHEME) --quiet)" = "#f" ] ; then \
		echo "ERROR: Chez is missing threading support" ; exit 1 ; fi
	mkdir -p bootstrap-build/idris2_app
	cp support/c/${IDRIS2_SUPPORT} bootstrap-build/idris2_app/
	sed 's/libidris2_support.so/${IDRIS2_SUPPORT}/g; s|__PREFIX__|${IDRIS2_BOOT_PREFIX}|g' \
		bootstrap/idris2_app/idris2.ss \
		> bootstrap-build/idris2_app/idris2-boot.ss
	$(SHELL) ./bootstrap-stage1-chez.sh
	IDRIS2_CG="chez" $(SHELL) ./bootstrap-stage2.sh

# Bootstrapping using racket
bootstrap-racket: support
	mkdir -p bootstrap-build/idris2_app
	cp support/c/${IDRIS2_SUPPORT} bootstrap-build/idris2_app/
	sed 's|__PREFIX__|${IDRIS2_BOOT_PREFIX}|g' \
		bootstrap/idris2_app/idris2.rkt \
		> bootstrap-build/idris2_app/idris2-boot.rkt
	$(SHELL) ./bootstrap-stage1-racket.sh
	IDRIS2_CG="racket" $(SHELL) ./bootstrap-stage2.sh

bootstrap-test:
	$(MAKE) test INTERACTIVE='' IDRIS2_PREFIX=${IDRIS2_BOOT_PREFIX}

ci-windows-bootstrap-test:
	$(MAKE) test except="idris2/repl005" INTERACTIVE='' IDRIS2_PREFIX=${IDRIS2_BOOT_PREFIX}

bootstrap-clean:
	$(RM) -r bootstrap-build


.PHONY: distclean

distclean: clean bootstrap-clean
	@find . -type f -name '*.ttc' -exec rm -f {} \;
	@find . -type f -name '*.ttm' -exec rm -f {} \;
	@find . -type f -name '*.ibc' -exec rm -f {} \;
