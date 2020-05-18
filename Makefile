include config.mk

# Idris 2 executable used to bootstrap
IDRIS2_BOOT ?= idris2

# Idris 2 executable we're building
NAME = idris2sh
TARGETDIR = build/exec
TARGET = ${TARGETDIR}/${NAME}

MAJOR=0
MINOR=2
PATCH=0

GIT_SHA1=
VER_TAG=
ifeq ($(shell git status >/dev/null 2>&1; echo $$?), 0)
    # inside a git repo
    ifneq ($(shell git describe --exact-match --tags >/dev/null 2>&1; echo $$?), 0)
        # not tagged as a released version, so add sha1 of this build in between releases
        GIT_SHA1 := $(shell git rev-parse --short=9 HEAD)
        VER_TAG := -${GIT_SHA1}
    endif
endif

export IDRIS2_SUPPORT := libidris2_support${SHLIB_SUFFIX}
export IDRIS2_VERSION := ${MAJOR}.${MINOR}.${PATCH}
IDRIS2_VERSION_TAG := ${IDRIS2_VERSION}${VER_TAG}

export IDRIS2_CURDIR = $(CURDIR)
export IDRIS2_BOOT_PATH = ${IDRIS2_CURDIR}/libs/prelude/build/ttc:${IDRIS2_CURDIR}/libs/base/build/ttc:${IDRIS2_CURDIR}/libs/network/build/ttc

.PHONY: all support clean support-clean init-bootstrap ${TARGET}

all: support ${TARGET} libs

${TARGET}:
	${IDRIS2_BOOT} --build idris2.ipkg

prelude:
	${MAKE} -C libs/prelude IDRIS2=../../${TARGET} IDRIS2_PATH=${IDRIS2_BOOT_PATH}

base: prelude
	${MAKE} -C libs/base IDRIS2=../../${TARGET} IDRIS2_PATH=${IDRIS2_BOOT_PATH}

network: prelude
	${MAKE} -C libs/network IDRIS2=../../${TARGET} IDRIS2_PATH=${IDRIS2_BOOT_PATH}
	${MAKE} -C libs/network test IDRIS2=../../${TARGET} IDRIS2_PATH=${IDRIS2_BOOT_PATH}

contrib: prelude
	${MAKE} -C libs/contrib IDRIS2=../../${TARGET} IDRIS2_PATH=${IDRIS2_BOOT_PATH}

libs : prelude base network contrib

support:
	@${MAKE} -C support/c

support-clean:
	@${MAKE} -C support/c clean

clean-libs:
	${MAKE} -C libs/prelude clean
	${MAKE} -C libs/base clean
	${MAKE} -C libs/network clean
	${MAKE} -C libs/contrib clean

clean: clean-libs support-clean
	${IDRIS2_BOOT} --clean idris2.ipkg
	rm -rf ${TARGETDIR}

install: install-idris2 install-support install-libs

install-idris2:
	mkdir -p ${PREFIX}/bin/${NAME}_app
	install ${TARGET} ${PREFIX}/bin
	install ${TARGETDIR}/${NAME}_app/* ${PREFIX}/bin/${NAME}_app

install-support: support
	mkdir -p ${PREFIX}/idris2-${IDRIS2_VERSION}/support/chez
	mkdir -p ${PREFIX}/idris2-${IDRIS2_VERSION}/support/racket
	mkdir -p ${PREFIX}/idris2-${IDRIS2_VERSION}/support/gambit
	install support/chez/* ${PREFIX}/idris2-${IDRIS2_VERSION}/support/chez
	install support/racket/* ${PREFIX}/idris2-${IDRIS2_VERSION}/support/racket
	install support/gambit/* ${PREFIX}/idris2-${IDRIS2_VERSION}/support/gambit
	@${MAKE} -C support/c install

install-libs: libs
	${MAKE} -C libs/prelude install IDRIS2=../../${TARGET} IDRIS2_PATH=${IDRIS2_BOOT_PATH}
	${MAKE} -C libs/base install IDRIS2=../../${TARGET} IDRIS2_PATH=${IDRIS2_BOOT_PATH}
	${MAKE} -C libs/network install IDRIS2=../../${TARGET} IDRIS2_PATH=${IDRIS2_BOOT_PATH} IDRIS2_VERSION=${IDRIS2_VERSION}
	${MAKE} -C libs/contrib install IDRIS2=../../${TARGET} IDRIS2_PATH=${IDRIS2_BOOT_PATH}

init-bootstrap:
	./init-bootstrap
