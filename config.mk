##### Options which a user might set before building go here #####

# Where to install idris2 binaries and libraries
PREFIX ?= $(HOME)/.idris2

# For Windows targets. Set to 1 to support Windows 7.
OLD_WIN ?= 0

##################################################################

RANLIB ?= ranlib
AR ?= ar

CFLAGS := -Wall $(CFLAGS)
LDFLAGS := $(LDFLAGS)

MACHINE := $(shell $(CC) -dumpmachine)
ifneq (,$(findstring cygwin, $(MACHINE)))
	OS := windows
	SHLIB_SUFFIX := .dll
else ifneq (,$(findstring mingw, $(MACHINE)))
	OS := windows
	SHLIB_SUFFIX := .dll
else ifneq (,$(findstring windows, $(MACHINE)))
	OS := windows
	SHLIB_SUFFIX := .dll
else ifneq (,$(findstring darwin, $(MACHINE)))
	OS := darwin
	SHLIB_SUFFIX := .dylib
	CFLAGS += -fPIC
else ifneq (, $(findstring bsd, $(MACHINE)))
	OS := bsd
	SHLIB_SUFFIX := .so
	CFLAGS += -fPIC
else
	OS := linux
	SHLIB_SUFFIX := .so
	CFLAGS += -fPIC
endif
export OS

ifeq ($(OS),bsd)
	MAKE := gmake
else
	MAKE := make
endif
export MAKE

# Add a custom.mk file to override any of the configurations
-include custom.mk
