include config.mk

# Idris 2 executable used to bootstrap
export IDRIS2_BOOT ?= idris2

# Idris 2 executable we're building
NAME = idris2
TARGETDIR = build/exec
TARGET = ${TARGETDIR}/${NAME}

MAJOR=0
MINOR=2
PATCH=0

GIT_SHA1=
ifeq ($(shell git status >/dev/null 2>&1; echo $$?), 0)
    # inside a git repo
    ifneq ($(shell git describe --exact-match --tags >/dev/null 2>&1; echo $$?), 0)
        # not tagged as a released version, so add sha1 of this build in between releases
        GIT_SHA1 := $(shell git rev-parse --short=9 HEAD)
    endif
endif

export IDRIS2_VERSION := ${MAJOR}.${MINOR}.${PATCH}
IDRIS2_SUPPORT := libidris2_support${SHLIB_SUFFIX}

CG ?= ${IDRIS2_CG}
ifneq (${CG},racket)
    IDRIS2_IPKG := idris2.ipkg
else
    IDRIS2_IPKG := idris2rkt.ipkg
endif

export IDRIS2_BOOT_PATH = ${CURDIR}/libs/prelude/build/ttc:${CURDIR}/libs/base/build/ttc:${CURDIR}/libs/network/build/ttc

export SCHEME


.PHONY: all idris2-exec ${TARGET} support support-clean clean distclean

all: support ${TARGET} libs

idris2-exec: ${TARGET}

${TARGET}: src/IdrisPaths.idr
	${IDRIS2_BOOT} --build ${IDRIS2_IPKG}

src/IdrisPaths.idr:
	echo 'module IdrisPaths' > src/IdrisPaths.idr
	echo 'export idrisVersion : ((Nat,Nat,Nat), String); idrisVersion = ((${MAJOR},${MINOR},${PATCH}), "${GIT_SHA1}")' >> src/IdrisPaths.idr
	echo 'export yprefix : String; yprefix="${PREFIX}"' >> src/IdrisPaths.idr

prelude:
	${MAKE} -C libs/prelude IDRIS2=../../${TARGET} IDRIS2_PATH=${IDRIS2_BOOT_PATH}

base: prelude
	${MAKE} -C libs/base IDRIS2=../../${TARGET} IDRIS2_PATH=${IDRIS2_BOOT_PATH}

network: prelude
	${MAKE} -C libs/network IDRIS2=../../${TARGET} IDRIS2_PATH=${IDRIS2_BOOT_PATH}

contrib: prelude
	${MAKE} -C libs/contrib IDRIS2=../../${TARGET} IDRIS2_PATH=${IDRIS2_BOOT_PATH}

libs : prelude base network contrib

test:
	@${MAKE} -C tests only=$(only) IDRIS2=../../../${TARGET}

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
	-${IDRIS2_BOOT} --clean ${IDRIS2_IPKG}
	$(RM) src/IdrisPaths.idr
	${MAKE} -C tests clean
	$(RM) -r build

install: install-idris2 install-support install-libs

install-api:
	${IDRIS2_BOOT} --install idris2api.ipkg

install-idris2:
	mkdir -p ${PREFIX}/bin/
	install ${TARGET} ${PREFIX}/bin
	mkdir -p ${PREFIX}/lib/
	install support/c/${IDRIS2_SUPPORT} ${PREFIX}/lib
ifneq ($(CG),racket)
	mkdir -p ${PREFIX}/bin/${NAME}_app
	install ${TARGETDIR}/${NAME}_app/* ${PREFIX}/bin/${NAME}_app
endif

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


.PHONY: bootstrap bootstrap-racket bootstrap-clean

bootstrap: support
	cp support/c/${IDRIS2_SUPPORT} bootstrap/idris2_app
	sed s/libidris2_support.so/${IDRIS2_SUPPORT}/g bootstrap/idris2_app/idris2.ss > bootstrap/idris2_app/idris2-boot.ss
ifeq ($(OS), darwin)
	sed -i '' 's|__PREFIX__|${CURDIR}/bootstrap|g' bootstrap/idris2_app/idris2-boot.ss
else
	sed -i 's|__PREFIX__|${CURDIR}/bootstrap|g' bootstrap/idris2_app/idris2-boot.ss
endif
	sh ./bootstrap.sh

bootstrap-racket: support
	cp support/c/${IDRIS2_SUPPORT} bootstrap/idris2_app
	cp bootstrap/idris2.rkt bootstrap/idris2boot.rkt
ifeq ($(OS), darwin)
	sed -i '' 's|__PREFIX__|${CURDIR}/bootstrap|g' bootstrap/idris2boot.rkt
else
	sed -i 's|__PREFIX__|${CURDIR}/bootstrap|g' bootstrap/idris2boot.rkt
endif
	sh ./bootstrap-rkt.sh

bootstrap-clean:
	$(RM) -r bootstrap/bin bootstrap/lib bootstrap/idris2-${IDRIS2_VERSION}
	$(RM) bootstrap/idris2boot* bootstrap/idris2_app/idris2-boot.* bootstrap/idris2_app/${IDRIS2_SUPPORT}


.PHONY: distclean

distclean: clean bootstrap-clean
	@find . -type f -name '*.ttc' -exec rm -f {} \;
	@find . -type f -name '*.ttm' -exec rm -f {} \;
	@find . -type f -name '*.ibc' -exec rm -f {} \;
