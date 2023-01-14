##### Options which a user might set before building go here #####

# Where to install idris2 binaries and libraries (must be an absolute path)
PREFIX ?= $(HOME)/.idris2

# For Windows targets. Set to 1 to support Windows 7.
OLD_WIN ?= 0

##################################################################

RANLIB ?= ranlib
AR ?= ar

CFLAGS := -Wall $(CFLAGS)
CPPFLAGS := $(CPPFLAGS)
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
else ifneq (, $(findstring bsd, $(MACHINE)))
	OS := bsd
	SHLIB_SUFFIX := .so
else
	OS := linux
	SHLIB_SUFFIX := .so
endif

ifneq (, $(findstring freebsd, $(MACHINE)))
	CFLAGS += -I$(shell /sbin/sysctl -n user.localbase)/include
	LDFLAGS += -L$(shell /sbin/sysctl -n user.localbase)/lib
endif

ifneq ($(OS),windows)
	CFLAGS += -fPIC
else ifneq (, $(findstring NT-6.1,$(shell uname)))
	OLD_WIN = 1
endif

ifeq ($(OS),bsd)
	MAKE := gmake
else
	MAKE := make
endif

export OS MAKE OLD_WIN

# Add a custom.mk file to override any of the configurations
-include custom.mk
