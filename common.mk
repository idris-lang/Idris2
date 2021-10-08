# This file is included by all Makefiles, but users should edit
# config.mk instead, so that git won't see pending changes. A
# config.mk.sample is provided.

-include config.mk

# Set some defaults if not set by config.mk.
PREFIX ?= $(HOME)/.idris2
CHEZ ?= scheme
RACKET_RACO ?= raco
IDRIS2_CG ?= chez
OLD_WIN ?= 0
DEBUG_IDRIS_BUILD_SYSTEM ?=

# Make sure it's an absolute path, because it will be inserted into #!
# shell headers. The 'override' is needed for the case when it's
# specified as `make CHEZ=foo bootstrap`, e.g. as in the nix build.
override CHEZ := $(shell command -v $(CHEZ) 2>/dev/null)

# Idris 2 executable we're building
NAME = idris2

RANLIB ?= ranlib
AR ?= ar

CFLAGS := -Wall $(CFLAGS)
LDFLAGS := $(LDFLAGS)

empty :=
space := $(empty) $(empty)

EXE_SUFFIX :=
SHLIB_SUFFIX := .so

MACHINE := $(shell $(CC) -dumpmachine)
ifneq (,$(findstring cygwin, $(MACHINE)))
	OS := windows
	SHLIB_SUFFIX := .dll
	EXE_SUFFIX := .exe
else ifneq (,$(findstring mingw, $(MACHINE)))
	OS := windows
	SHLIB_SUFFIX := .dll
	EXE_SUFFIX := .exe
else ifneq (,$(findstring windows, $(MACHINE)))
	OS := windows
	SHLIB_SUFFIX := .dll
	EXE_SUFFIX := .exe
else ifneq (,$(findstring darwin, $(MACHINE)))
	OS := darwin
	SHLIB_SUFFIX := .dylib
else ifneq (, $(findstring bsd, $(MACHINE)))
	OS := bsd
else
	OS := linux
endif

ifneq ($(OS),windows)
	CFLAGS += -fPIC
else ifneq (, $(findstring NT-6.1,$(shell uname)))
	OLD_WIN = 1
endif

ifeq ($(OS),windows)
  # This produces D:/../.. style paths
  IDRIS2_PREFIX := $(shell cygpath -m ${PREFIX})
  IDRIS2_CURDIR := $(shell cygpath -m ${CURDIR})
  SEP := ;
else
  IDRIS2_PREFIX := ${PREFIX}
  IDRIS2_CURDIR := ${CURDIR}
  SEP := :
endif

export OS OLD_WIN

ifeq ($(IDRIS2_CG),chez)
  ifeq (,$(shell command -v "$(CHEZ)"))
    $(warning The CHEZ variable should point to a working Chez Scheme executable.)
  endif
else ifeq ($(IDRIS2_CG),racket)
  ifeq (,$(shell command -v "$(RACKET_RACO)"))
    $(warning The RACKET_RACO variable should point to a working raco executable of Racket.)
  endif
endif

ifneq ($(DEBUG_IDRIS_BUILD_SYSTEM),)
  $(info OS=[$(OS)], EXE_SUFFIX=[$(EXE_SUFFIX)], SHLIB_SUFFIX=[$(SHLIB_SUFFIX)], OLD_WIN=[$(OLD_WIN)], CHEZ=[$(CHEZ)], RACKET_RACO=[$(RACKET_RACO)], IDRIS2_CG=[$(IDRIS2_CG)], PREFIX=[$(PREFIX)], BOOTSTRAP_IDRIS=[$(BOOTSTRAP_IDRIS)].)
endif

# Add a custom.mk file to override any of the configurations
-include custom.mk
