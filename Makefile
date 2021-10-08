include common.mk

# Examples:
#  - Build stage0 and then use it to build stage1 (as opposed to
#    bootstrapping it from Scheme):
#      make STAGE0_GIT_REF=v0.5.1 stage1
#
#  - Build stage1 using an external Idris binary, and prepare the
#    bootstrap files for commit:
#      make distclean
#      make BOOTSTRAP_IDRIS=idris2-0.5.1 IDRIS2_CG=chez stage1 stage2 && make BOOTSTRAP_IDRIS=idris2-0.5.1 IDRIS2_CG=racket stage1 stage2 && make prepare-bootstrap-files
#
#  - Bootstrap stage1 from the checked in Scheme sources:
#      make stage1 (its behavior depends on the config in the makefile)
#      make bootstrap (run the bootstrap unconditionally)

BUILD ?= build

# When the STAGE0_GIT_REF variable is empty, then we will
# automatically resort to taking a bootstrap shortcut as a means of
# building stage 1 by using the CHEZ binary to compile the checked in
# scheme output of the chez CG; i.e. stage 0 will be completely
# skipped (and thus you won't be able to regenerate the bootstrap
# shortcut files of stage 1 this way).
#
# It's better to keep this variable emtpy in the repo, and only edit
# it locally when someone wants to regenerate the bootstrap shortcut
# files. Rationale: most people who check out the repo don't want the
# extra time to compile stage 0.

STAGE0_GIT_REF=
#STAGE0_GIT_REF ?= v0.5.1

# We allow overriding STAGE0_IDRIS with an external executable.
ifneq ($(BOOTSTRAP_IDRIS),)
  # We were given an external binary
  STAGE0=
  STAGE0_IDRIS=
  STAGE1_PREREQUISITES=
else ifneq ($(STAGE0_GIT_REF),)
  # We know how to build stage 0 from the git ref
  STAGE0=$(BUILD)/stage0
  STAGE0_IDRIS=$(STAGE0)/installed/bin/$(NAME)
  STAGE1_PREREQUISITES=$(STAGE0_IDRIS)
else
  # The only way to get going is through the bootstrap target.
  STAGE0=
  STAGE0_IDRIS=
  STAGE1_PREREQUISITES=
endif

STAGE1 ?= $(BUILD)/stage1
STAGE2 ?= $(BUILD)/stage2
STAGE3 ?= $(BUILD)/stage3

STAGE1_IDRIS ?= $(STAGE1)/installed/bin/$(NAME)
STAGE2_IDRIS  = $(STAGE2)/installed/bin/$(NAME)
STAGE3_IDRIS  = $(STAGE3)/installed/bin/$(NAME)

# This is a descriptve tag. If e.g. git returns 'v0.5.1-19-g6bb9ddd0b-dirty'
# then this var will contain '19-g6bb9ddd0b-dirty'.
export IDRIS_VERSION_TAG ?= $(subst $(space),-,$(wordlist 2,10,$(subst -, ,$(shell git describe --tags --dirty))))
# This extracts only the tag name, i.e. v1.2.3
export IDRIS_VERSION     ?= $(shell git describe --tags --abbrev=0)
ifeq ($(IDRIS_VERSION),)
  $(error "Couldn't run the git binary to extract the version. Either build in a directory \
with an intact .git/ database, and a functional git binary in the PATH, or set the following \
variables by hand; e.g.: make all IDRIS_VERSION=v1.2.3 IDRIS_VERSION_TAG=")
else
  $(info Idris Makefile invoked; version [$(IDRIS_VERSION)], version tag [$(IDRIS_VERSION_TAG)].)
endif

export IDRIS_FULL_VERSION := $(IDRIS_VERSION)$(if $(IDRIS_VERSION_TAG),-$(IDRIS_VERSION_TAG))

define make-stage-generic
  $(MAKE) --makefile one-stage.mk \
    BOOTSTRAP_IDRIS="$(if $(1),$(abspath $(1)/bin/$(NAME)),$(BOOTSTRAP_IDRIS))" \
    BUILD=$(2) \
    PREFIX="$(3)" \
    IDRIS2_CG=$(IDRIS2_CG) \
    $(4) $(5) $(6) $(7) $(8)
endef

define make-stage
  $(call make-stage-generic,$(if $(1),$(1)/installed),$(2),$(abspath $(2)/installed),$(3),$(4),$(5),$(6),$(7),$(8))
endef

all: stage2

$(BUILD):
	mkdir -p $@

$(STAGE0)/src-$(STAGE0_GIT_REF):
	git worktree add --detach --force $@ $(STAGE0_GIT_REF)

stage0 $(STAGE0_IDRIS): $(STAGE0)/src-$(STAGE0_GIT_REF)
	@echo -e "\n*** Building the bootstrap host (aka stage 0); STAGE0_GIT_REF=$(STAGE0_GIT_REF)\n"
	$(MAKE) --directory $< SCHEME="$(CHEZ)" PREFIX="$(abspath $(STAGE0)/installed)" bootstrap install

# We don't FORCE stage1, which means that it only gets rebuilt after a
# make clean. Also note that stage0 is only part of the prerequisites
# when we are not taking a bootstrap shortcut.
stage1 $(STAGE1_IDRIS): $(STAGE1_PREREQUISITES)
	@echo -e "\n*** Building stage 1 using [$(or $(STAGE0_GIT_REF),\
$(BOOTSTRAP_IDRIS),bootstrap files)]\n"
	$(if $(or $(STAGE0_GIT_REF),$(BOOTSTRAP_IDRIS)), \
          $(call make-stage,$(STAGE0),$(STAGE1),all,install), \
          $(MAKE) bootstrap)

stage2 $(STAGE2_IDRIS): FORCE $(STAGE1_IDRIS)
	@echo -e "\n*** Building stage 2\n"
	$(call make-stage,$(STAGE1),$(STAGE2),all,install)

stage3 $(STAGE3_IDRIS): FORCE $(STAGE2_IDRIS)
	@echo -e "\n*** Building stage 3\n"
	$(call make-stage,$(STAGE2),$(STAGE3),all,install)

# ChezScheme's compile-file doesn't produce reproducible output, so we
# need to skip *.so files for now.
#
# Note that this target is only meaningful if stage 1 is up to date,
# i.e. only when not taking a bootstrap shortcut and stage 1 is the
# result of compiling the latest in src/.
check-reproducibility: $(STAGE3_IDRIS)
	@if diff --recursive --new-file --exclude=*.so $(STAGE2) $(STAGE3); then \
          @echo -e "\nstage2 and stage3 has the above listed differences.\n\
Note, that the check-reproducibility target only makes sense when \
stage1 has been freshly built by stage0 (as opposed to `make bootstrap`ped from \
the potentially outdated Scheme sources checked into the repo); i.e. \
1) make distclean && make BOOTSTRAP_IDRIS=idris2-0.5.1 stage1 \
2) make distclean && make STAGE0_GIT_REF=v0.5.1 stage1\n" \
          echo -e ""; \
        fi

support-clean:
	@$(MAKE) -C support/c    clean
	@$(MAKE) -C support/refc clean
	@$(MAKE) -C support/chez clean

test-clean:
	$(RM) tests/failures
	$(RM) -r tests/build
	$(RM) -r tests/**/**/build
	@find tests/ -type f -name 'output' -exec rm -rf {} \;
	@find tests/ -type f -name '*.ttc' -exec rm -f {} \;
	@find tests/ -type f -name '*.ttm' -exec rm -f {} \;
	@find tests/ -type f -name '*.ibc' -exec rm -f {} \;

clean: support-clean test-clean
	$(if $(or $(STAGE0_GIT_REF),$(BOOTSTRAP_IDRIS)),$(RM) -r $(STAGE1))
	$(RM) -r $(STAGE2) $(STAGE3) $(RELEASE_DIR)

# Forward these blindly in the context of STAGE1.
test retest idris2-exec libs libdocs support:
	$(call make-stage,$(STAGE1),$(STAGE2),$(MAKECMDGOALS))

# TODO it would be safer if all the sed calls below failed loudly when
# a match was not found.
bootstrap: FORCE
	@echo -e "\nbootstrap target is initiated\n"
# We need to cater for Windows here, hence the use of IDRIS2_CURDIR,
# instead of using $(abspath $(STAGE1)/installed).
	mkdir -p $(STAGE1)
	cp -r bootstrap/* $(STAGE1)/
	sed -i -e 's|__PREFIX__|$(IDRIS2_CURDIR)/$(STAGE1)/installed|g' \
	  $(STAGE1)/$(NAME)_app/$(NAME).ss \
	  $(STAGE1)/$(NAME)_app/$(NAME).rkt
	sed -i -e 's|__CHEZ__ |$(CHEZ) |g; s|libidris2_support.so|libidris2_support$(SHLIB_SUFFIX)|g' \
	  $(STAGE1)/$(NAME)_app/$(NAME).ss
	$(call make-stage,$(STAGE0),$(STAGE1),bootstrap)
	$(call make-stage,$(STAGE0),$(STAGE1),all,install)
# We clear STAGE0_GIT_REF to make sure that stage0 is ignored.
	$(MAKE) STAGE0_GIT_REF= $(STAGE2_IDRIS)

# It takes a snapshot of the stage 2 build artifacts in the build dir
# of stage 1, and prepares them for a git commit.
prepare-bootstrap-files:
	@echo -e "\nWARNING: this target depends on stage 2 but does not rebuild it \
automatically. Make sure that you have built with all the CG's that you want to commit \
(i.e. make IDRIS2_CG=racket stage2, etc.)\n"
	cp $(STAGE2)/$(NAME) bootstrap/
	cp $(STAGE2)/$(NAME)_app/$(NAME).* bootstrap/$(NAME)_app/
	sed -i -e 's|$(IDRIS2_CURDIR)/$(STAGE2)/installed|__PREFIX__|' \
	  bootstrap/$(NAME)_app/$(NAME).ss \
	  bootstrap/$(NAME)_app/$(NAME).rkt
	sed -i -e '1,2{s|^#!.*scheme --program|#!__CHEZ__ --program|}' \
	  bootstrap/$(NAME)_app/$(NAME).ss
	git add \
	  bootstrap/$(NAME) \
	  bootstrap/$(NAME)_app/$(NAME).ss \
	  bootstrap/$(NAME)_app/$(NAME).rkt
	@echo "The bootstrap shortcut files have been added to the git index, ready to be committed."

RELEASE_DIR_NAME := Idris2-$(IDRIS_FULL_VERSION)
RELEASE_DIR      := $(BUILD)/$(RELEASE_DIR_NAME)
RELEASE_ARCHIVE  := idris2-$(IDRIS_FULL_VERSION).tgz

$(RELEASE_DIR):
	mkdir -p $(RELEASE_DIR)
	git worktree add --detach --force $(RELEASE_DIR) HEAD
        # Pin the version variables in config.mk, so that building the
        # release tarball doesn't require git.
	echo "IDRIS_VERSION:=$(IDRIS_VERSION)" >>$(RELEASE_DIR)/config.mk
	echo "IDRIS_VERSION_TAG:=$(IDRIS_VERSION_TAG)" >>$(RELEASE_DIR)/config.mk
	$(RM) -r $(RELEASE_DIR)/.git* $(RELEASE_DIR)/Release $(RELEASE_DIR)/benchmark
	find $(RELEASE_DIR) -type f -name '.gitignore' -exec rm -f "{}" \;

release $(BUILD)/$(RELEASE_ARCHIVE): $(RELEASE_DIR)
	tar -C $(BUILD) -zcf $(RELEASE_ARCHIVE) $(RELEASE_DIR_NAME)
	@echo -e "\n$(RELEASE_ARCHIVE) created.\n"

install install-with-src-libs install-libdocs:
	$(call make-stage-generic,$(STAGE1)/installed,$(STAGE2),$(PREFIX),$(MAKECMDGOALS))

# The API is the sources of the compiler, therefore the API targets
# use BOOTSTRAP_IDRIS (i.e. stage n-1) for compilation.  Therefore we
# must do a +1 shift here compared to the above install targets
# (i.e. API is stage2->stage3, not stage1->stage2), so that the .ttc
# files are produced by the latest version of the compiler (i.e. they
# have the proper version, and we don't get a "TTC data is in an newer
# format" error). This is needed because stage 1 may be a somewhat
# older version than HEAD, depending on what version has been last
# captured to be the bootstrap shortcut, or what state of the codebase
# was compiled into a stage 1 binary.
#
# TODO FIXME KLUDGE this target requires that stage2 is already
# installed into the same destination dir where we want to install the
# API. It uses the installed binary and libs to compile and install
# the API. See note in the stage makefile for the details of this
# handicap.
#
# When this gets fixed then something like the following should suffice:
# $(call make-stage-generic,$(STAGE2)/installed,$(STAGE3),$(PREFIX),$(MAKECMDGOALS))
install-api install-with-src-api:
# with the following line it's possible to invoke `make install-api` on a fresh checkout.
#	$(call make-stage-generic,$(STAGE1)/installed,$(STAGE2),$(PREFIX),all,install)
	@echo "\nWARNING: for now this target only works when Idris2 has already been \
installed in the destination.\n"
	$(call make-stage-generic,$(PREFIX),$(STAGE3),$(PREFIX),$(MAKECMDGOALS))

distclean: clean
	$(RM) -r $(BUILD) docs/build/
	@find tests/ -type f -name '*.ttc' -exec rm -f {} \;
	@find tests/ -type f -name '*.ttm' -exec rm -f {} \;
	@find tests/ -type f -name '*.ibc' -exec rm -f {} \;
# Let's also -print the matches, so that we notice when some build
# output gets written into the source directories.
	@find . -type f -name '*.ttc' -print -exec rm -f {} \;
	@find . -type f -name '*.ttm' -print -exec rm -f {} \;
	@find . -type f -name '*.ibc' -print -exec rm -f {} \;

FORCE:
