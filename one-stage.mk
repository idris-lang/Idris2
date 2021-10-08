# This makefile is called by the toplevel Makefile. The following
# variables are used to communicate the arguments:
#   BUILD
#   PREFIX            - where to install
#   IDRIS2            - the binary to use for flexible targets like e.g. test
#   IDRIS2_CG
#   BOOTSTRAP_IDRIS   - the binary of the previous stage. may be undefined, so be
#                       mindful with $(shell ...)! also, don't quote it, because the
#                       CI calls it as BOOTSTRAP_IDRIS="idris2 -Werror".
#   IDRIS_VERSION     - e.g. v0.5.1
#   IDRIS_VERSION_TAG - e.g. 19-g6bb9ddd0b-dirty
#   IDRIS_FULL_VERSION - e.g. v0.5.1-19-g6bb9ddd0b-dirty

include common.mk

BUILD ?= build
TARGETDIR ?= $(BUILD)
TARGET = $(TARGETDIR)/$(NAME)

IDRIS2 ?= $(TARGET)

VERSION_PIECES    := $(subst ., ,$(subst v,,$(IDRIS_VERSION)))
V_MAJOR           := $(word 1,$(VERSION_PIECES))
V_MINOR           := $(word 2,$(VERSION_PIECES))
V_PATCH           := $(word 3,$(VERSION_PIECES))
export IDRIS_INSTALL_DIR := $(NAME)-$(V_MAJOR).$(V_MINOR).$(V_PATCH)

IDRIS2_SUPPORT := libidris2_support$(SHLIB_SUFFIX)
IDRIS2_APP_IPKG := idris2.ipkg
IDRIS2_LIB_IPKG := idris2api.ipkg

$(info Stage Makefile invoked, BUILD=[$(BUILD)], PREFIX=[$(PREFIX)], \
  IDRIS2_PREFIX=[$(IDRIS2_PREFIX)], BOOTSTRAP_IDRIS=[$(BOOTSTRAP_IDRIS)], \
  MAKECMDGOALS=[$(MAKECMDGOALS)])

# IDRIS2_PREFIX is controlling the target of --install; TODO clean up this API?
# NOTE to cater for Windows we must use IDRIS2_CURDIR (as opposed to $(abspath ...))
INVOKE_IDRIS_NO_BUILD_DIR = IDRIS2_PREFIX="$(IDRIS2_PREFIX)" \
  IDRIS2_PATH="$(IDRIS2_CURDIR)/$(BUILD)/ttc" \
  IDRIS2_INC_CGS=$(IDRIS2_CG) "$(abspath $(IDRIS2))" \
  --output-dir "$(IDRIS2_CURDIR)/$(TARGETDIR)" \
  --codegen $(IDRIS2_CG)

INVOKE_IDRIS = $(INVOKE_IDRIS_NO_BUILD_DIR) --build-dir "$(IDRIS2_CURDIR)/$(BUILD)"

# NOTE It seems tempting to also set the IDRIS2_PREFIX here, but it
# cannot be due to the different contexts it is used in.
INVOKE_BOOTSTRAP_IDRIS = $(BOOTSTRAP_IDRIS) \
  --build-dir "$(IDRIS2_CURDIR)/$(BUILD)/bootstrap-host" \
  --output-dir "$(IDRIS2_CURDIR)/$(TARGETDIR)" \
  --codegen $(IDRIS2_CG)

.PHONY: all idris2-exec libdocs testenv support FORCE bootstrap

all: support $(TARGET) libs

idris2-exec: $(TARGET)

$(BUILD):
	mkdir -p $@

IDRIS_PATHS_FILE    := src/IdrisPaths.idr

define IDRIS_PATHS_BODY
-- @generated
module IdrisPaths

export idrisVersion : ((Nat,Nat,Nat), String)
idrisVersion = (($(V_MAJOR),$(V_MINOR),$(V_PATCH)), "$(IDRIS_VERSION_TAG)")

export yprefix : String
yprefix = "$(IDRIS2_PREFIX)"
endef

# We pass this through a shell variable to avoid escaping hell.
export IDRIS_PATHS_BODY

# We use FORCE to always rebuild IdrisPath so that the git SHA1 info
# is always up to date, but only touch the output file when it has
# actually changed, to avoid unnecessary recompilations.
$(IDRIS_PATHS_FILE): FORCE
	@mkdir -p $(dir $(IDRIS_PATHS_FILE))
	@echo "$${IDRIS_PATHS_BODY}" >$(IDRIS_PATHS_FILE).new
	@if ! cmp -s $(IDRIS_PATHS_FILE) $(IDRIS_PATHS_FILE).new; then \
	  mv $(IDRIS_PATHS_FILE).new $(IDRIS_PATHS_FILE); \
	  echo -e "Updated $(IDRIS_PATHS_FILE) to:\n"; \
          cat $(IDRIS_PATHS_FILE); \
	else \
	  rm $(IDRIS_PATHS_FILE).new; \
	fi

# Splitting this part into more refined steps enables us to just
# commit the intermediate build artifacts in the build/ directory as a
# means of capturing the neccesary files for a bootstrap shortcut.

# These rules could live next to each other, theoretically, but I don't know how
# to tell make's rule engine which path to choose when generating the exe; hence
# the conditional definition.
TARGET_REAL := $(TARGETDIR)/$(NAME)_app/$(NAME)$(EXE_SUFFIX)
ifeq ($(IDRIS2_CG),chez)
  TARGET_REAL := $(TARGETDIR)/$(NAME)_app/$(NAME)
  # No $(EXE_SUFFIX) here because the output of the Chez backend is a shebang
  # prefixed script.
  $(TARGETDIR)/% : $(TARGETDIR)/%.ss
	@if [ "$$(echo '(threaded?)' | $(CHEZ) --quiet)" = "#f" ] ; then \
		echo "ERROR: Chez is missing threading support" ; exit 1 ; fi
	echo "(parameterize ([optimize-level 3]) (compile-program \"$<\" \"$@\"))" | "$(CHEZ)"
else ifeq ($(IDRIS2_CG),racket)
  $(TARGETDIR)/%$(EXE_SUFFIX) : $(TARGETDIR)/%.rkt
	"$(RACKET_RACO)" exe -o $@ $<
else ifeq ($(IDRIS2_CG),refc)
  $(TARGETDIR)/%$(EXE_SUFFIX) : $(TARGETDIR)/%.c
	ifeq ($(BOOTSTRAP_IDRIS),)
# TODO most of the time this will work, but strictly speaking, this is
# not sound, because here we should -I (and -L) from the version that
# was generating the output, i.e. that of the bootstrap host. IOW, we
# would need to also preserve the C support files and headers of the
# host that generated the refc output.
	  @echo "WARNING: taking a bootstrap shortcut through the refc CG \
             in the current setup is not sound. May work, but see the Makefile \
             for details."
	  $(CC) -x c -Werror -I support/refc \
	    -I support/c/include -std=c99 -O3 "$<"
	else
	  $(CC) -x c -Werror -I $(shell $(BOOTSTRAP_IDRIS) --libdir)/refc \
	    -I $(shell $(BOOTSTRAP_IDRIS) --libdir)/include -std=c99 -O3 "$<"
	endif
else
  $(error "Bootstrapping is not possible with the provided IDRIS2_CG: '$(IDRIS2_CG)'.")
endif

$(TARGET): $(TARGET_REAL)

# NOTE: we compile IdrisPaths.idr here and not in the target that
# generates it, so that no compilation is triggered while
# bootstrapping, because that would require a stage0 Idris executable.
$(TARGETDIR)/$(NAME)_app/$(NAME).ss \
$(TARGETDIR)/$(NAME)_app/$(NAME).rkt \
$(TARGETDIR)/$(NAME)_app/$(NAME).c : $(IDRIS_PATHS_FILE)
	@echo -e "\nCompiling Idris 2 version [$(IDRIS_FULL_VERSION)] using \
[$(BOOTSTRAP_IDRIS)], which is version [$$($(BOOTSTRAP_IDRIS) --version)] at \
[$$(command -v $(word 1,$(BOOTSTRAP_IDRIS)))]\n"
	$(if $(DEBUG_IDRIS_BUILD_SYSTEM),$(INVOKE_BOOTSTRAP_IDRIS) --paths)
        # KLUDGE: the CHEZ=true thing is a kludge to disable the
        # compilation step with Chez/Racket/cc, i.e. to let the
        # makefile do the final step in an effort to accommodate for
        # the in-place bootstrap shortcut setup.
	RACKET_RACO=true CHEZ=true IDRIS2_CC=true \
          $(INVOKE_BOOTSTRAP_IDRIS) --build $(IDRIS2_APP_IPKG)
        # Undo the above damage in the chez CG's output. TODO It would
        # be nice to only match the first line, and remain compatible
        # with non-GNU sed, but... MacOS sed is not GNU sed.
        # https://stackoverflow.com/questions/148451/how-to-use-sed-to-replace-only-the-first-occurrence-in-a-file
	sed -i -e 's|^#!true |#!$(CHEZ) |' $@
        # This is only needed on Windows: the #!/path/to/chez header
        # is missing from the chez compile-program output in
        # stage2. TODO Why? Simplify.
	sed -i -e 's|"true" --program|"$(CHEZ)" --program|' $(TARGET)
        # next release: the following sed call can be deleted
	sed -i -e 's|idris2\.so|idris2|' $(TARGET)

# The rest of the bootstrap process is in the main makefile.
bootstrap: $(IDRIS_PATHS_FILE)
	$(MAKE) -C support/c
        # To avoid triggering the rebuild of the .ss file.
        # FIXME get rid of IdrisPaths.idr, and then this touch can be deleted.
	touch $(TARGETDIR)/$(NAME)_app/$(NAME).ss \
              $(TARGETDIR)/$(NAME)_app/$(NAME).rkt \
              $(TARGETDIR)/$(NAME)_app/$(NAME).c
	install "support/c/$(IDRIS2_SUPPORT)" "$(TARGETDIR)/$(NAME)_app/"

libs: prelude base contrib network test-lib linear papers

prelude linear:
	cd libs/$@ && $(INVOKE_IDRIS) --build $@.ipkg

base: prelude
	cd libs/$@ && $(INVOKE_IDRIS) --build $@.ipkg

network: contrib
	cd libs/$@ && $(INVOKE_IDRIS) --build $@.ipkg

contrib: base
	cd libs/$@ && $(INVOKE_IDRIS) --build $@.ipkg

# There's an anomaly here, because there's already a target called 'test'.
# TODO resolve it by e.g. giving the test lib a proper name, like golden-tests?
test-lib: contrib
	cd libs/test && $(INVOKE_IDRIS) --build test.ipkg

papers: contrib linear
	cd libs/$@ && $(INVOKE_IDRIS) --build $@.ipkg

libdocs:
	cd libs/prelude && $(INVOKE_IDRIS_NO_BUILD_DIR) --build-dir $(abspath $(BUILD))/docs/prelude --mkdoc prelude.ipkg
	cd libs/base    && $(INVOKE_IDRIS_NO_BUILD_DIR) --build-dir $(abspath $(BUILD))/docs/base    --mkdoc base.ipkg
	cd libs/contrib && $(INVOKE_IDRIS_NO_BUILD_DIR) --build-dir $(abspath $(BUILD))/docs/contrib --mkdoc contrib.ipkg
	cd libs/network && $(INVOKE_IDRIS_NO_BUILD_DIR) --build-dir $(abspath $(BUILD))/docs/network --mkdoc network.ipkg
	cd libs/test    && $(INVOKE_IDRIS_NO_BUILD_DIR) --build-dir $(abspath $(BUILD))/docs/test    --mkdoc test.ipkg
	cd libs/linear  && $(INVOKE_IDRIS_NO_BUILD_DIR) --build-dir $(abspath $(BUILD))/docs/test    --mkdoc linear.ipkg

testenv:
	@echo
	@echo "NOTE: \`$(MAKE) test\` does not rebuild Idris or the libraries packaged with it; to do that run \`$(MAKE)\`"
	@if [ ! -x "$(IDRIS2)" ]; then echo "ERROR: IDRIS2 (whose value is $(IDRIS2)) doesn't point to an executable. Cannot run the tests!\n"; exit 1; fi
	@echo
	cd tests && $(INVOKE_IDRIS) --build tests.ipkg

INTERACTIVE ?= --interactive
THREADS ?= $(shell (nproc || sysctl -n hw.ncpu) 2>/dev/null || echo 1)

# We invoke `runtests` explicitly with `sh` to accommodate for Guix
# and NixOS where there are no /usr/bin/env or /bin/sh in their build
# sandbox.
RUN_TESTS = cd tests && IDRIS2_PREFIX="$(IDRIS2_PREFIX)" \
  IDRIS2_PATH="$(abspath $(BUILD)/ttc)" \
  sh "$(abspath $(TARGETDIR)/runtests)" "$(abspath $(IDRIS2))" $(INTERACTIVE) --timing --failure-file failures \
  --threads $(THREADS)

test: testenv
# NOTE: --only must be prior to --only-file, therefore it cannot be part of RUN_TESTS
	$(RUN_TESTS) --only $(only)

retest: testenv
	$(RUN_TESTS) --only-file failures --only $(only)

install: install-executable install-support install-libs

# TODO FIXME the IDRIS2_PREFIX env variable is controlling both the
# destination of installation and the source of libraries. Due to that
# this target only works after `make PREFIX=/path/dest install` has
# already been run, i.e. the compiled lib files were put to the same
# place where the API files are meant to be installed. Proposed fix:
# introduce DESTDIR variable that controls the install destination,
# and/or add a CLI argument for this.

# API is the sources of the compiler itself. To reuse the build
# artifacts, we use the bootstrap binary (i.e. stage n-1) to compile
# and install them.
build-api: $(IDRIS_PATHS_FILE)
	$(INVOKE_BOOTSTRAP_IDRIS) --build $(IDRIS2_LIB_IPKG)

install-api: build-api
	IDRIS2_PREFIX="$(IDRIS2_PREFIX)" $(INVOKE_BOOTSTRAP_IDRIS) --install $(IDRIS2_LIB_IPKG)

install-with-src-api: build-api
	IDRIS2_PREFIX="$(IDRIS2_PREFIX)" $(INVOKE_BOOTSTRAP_IDRIS) --install-with-src $(IDRIS2_LIB_IPKG)

# Ideally the install target shouldn't initiate a rebuild, but as long
# as the IdrisPaths.idr file is capturing the installation directory,
# we will need to make sure that it is updated with the current
# PREFIX, and the executabe is rebuilt to capture it.
install-executable: $(TARGET)
	mkdir -p "$(PREFIX)/bin/"
	install $(TARGET) "$(PREFIX)/bin"
ifeq ($(OS), windows)
	-install $(TARGET).cmd "$(PREFIX)/bin"
endif
	mkdir -p "$(PREFIX)/lib/"
	install support/c/$(IDRIS2_SUPPORT) "$(PREFIX)/lib"
	mkdir -p "$(PREFIX)/bin/$(NAME)_app"
	install $(TARGETDIR)/$(NAME)_app/* "$(PREFIX)/bin/$(NAME)_app"

support:
	@$(MAKE) -C support/c
	@$(MAKE) -C support/refc
	@$(MAKE) -C support/chez

install-support: support
	mkdir -p "$(PREFIX)/$(IDRIS_INSTALL_DIR)/support/docs"
	mkdir -p "$(PREFIX)/$(IDRIS_INSTALL_DIR)/support/racket"
	mkdir -p "$(PREFIX)/$(IDRIS_INSTALL_DIR)/support/gambit"
	mkdir -p "$(PREFIX)/$(IDRIS_INSTALL_DIR)/support/js"
	install -m 644 support/docs/*.css "$(PREFIX)/$(IDRIS_INSTALL_DIR)/support/docs"
	install -m 644 support/racket/*   "$(PREFIX)/$(IDRIS_INSTALL_DIR)/support/racket"
	install -m 644 support/gambit/*   "$(PREFIX)/$(IDRIS_INSTALL_DIR)/support/gambit"
	install -m 644 support/js/*       "$(PREFIX)/$(IDRIS_INSTALL_DIR)/support/js"
	@$(MAKE) -C support/c install
	@$(MAKE) -C support/refc install
	@$(MAKE) -C support/chez install

install-libs:
	cd libs/prelude && $(INVOKE_IDRIS) --install prelude.ipkg
	cd libs/base    && $(INVOKE_IDRIS) --install base.ipkg
	cd libs/contrib && $(INVOKE_IDRIS) --install contrib.ipkg
	cd libs/network && $(INVOKE_IDRIS) --install network.ipkg
	cd libs/test    && $(INVOKE_IDRIS) --install test.ipkg
	cd libs/linear  && $(INVOKE_IDRIS) --install linear.ipkg

install-with-src-libs:
	cd libs/prelude && $(INVOKE_IDRIS) --install-with-src prelude.ipkg
	cd libs/base    && $(INVOKE_IDRIS) --install-with-src base.ipkg
	cd libs/contrib && $(INVOKE_IDRIS) --install-with-src contrib.ipkg
	cd libs/network && $(INVOKE_IDRIS) --install-with-src network.ipkg
	cd libs/test    && $(INVOKE_IDRIS) --install-with-src test.ipkg
	cd libs/linear  && $(INVOKE_IDRIS) --install-with-src linear.ipkg

# TODO this could probably be simplified by emitting everything into
# $(BUILD)/docs/, and changing how doc links and files are generated.
install-libdocs: libdocs
	mkdir -p ${PREFIX}/${IDRIS_INSTALL_DIR}/docs/prelude
	mkdir -p ${PREFIX}/${IDRIS_INSTALL_DIR}/docs/base
	mkdir -p ${PREFIX}/${IDRIS_INSTALL_DIR}/docs/contrib
	mkdir -p ${PREFIX}/${IDRIS_INSTALL_DIR}/docs/network
	mkdir -p ${PREFIX}/${IDRIS_INSTALL_DIR}/docs/test
	mkdir -p ${PREFIX}/${IDRIS_INSTALL_DIR}/docs/linear
	cp -r $(BUILD)/docs/prelude/docs/* ${PREFIX}/${IDRIS_INSTALL_DIR}/docs/prelude
	cp -r $(BUILD)/docs/base/docs/*    ${PREFIX}/${IDRIS_INSTALL_DIR}/docs/base
	cp -r $(BUILD)/docs/contrib/docs/* ${PREFIX}/${IDRIS_INSTALL_DIR}/docs/contrib
	cp -r $(BUILD)/docs/network/docs/* ${PREFIX}/${IDRIS_INSTALL_DIR}/docs/network
	cp -r $(BUILD)/docs/test/docs/*    ${PREFIX}/${IDRIS_INSTALL_DIR}/docs/test
	cp -r $(BUILD)/docs/linear/docs/*  ${PREFIX}/${IDRIS_INSTALL_DIR}/docs/linear
	install -m 644 support/docs/*      ${PREFIX}/${IDRIS_INSTALL_DIR}/docs

FORCE:
