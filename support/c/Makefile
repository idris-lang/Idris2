include ../../config.mk

TARGET = libidris2_support

LIBTARGET = $(TARGET).a
DYLIBTARGET = $(TARGET)$(SHLIB_SUFFIX)

SRCS := $(wildcard *.c)
OBJS = $(SRCS:.c=.o)
DEPS = $(OBJS:.o=.d)

CFLAGS += -O2

ifeq ($(OS), windows)
	SRCS += windows/win_utils.c windows/win_hack.c
	CPPFLAGS += -DWIN32_LEAN_AND_MEAN
	LDFLAGS += -lws2_32
ifeq ($(OLD_WIN), 1)
	CPPFLAGS += -D_OLD_WIN
endif
endif


.PHONY: all
all: build

.PHONY: build
build: $(LIBTARGET) $(DYLIBTARGET)

$(LIBTARGET): $(OBJS)
	$(AR) rc $@ $^
	$(RANLIB) $@

$(DYLIBTARGET): $(OBJS)
	$(CC) $(CFLAGS) $(CPPFLAGS) -shared -o $@ $^ $(LDFLAGS)

-include $(DEPS)

%.d: %.c
	@$(CPP) $(CPPFLAGS) $< -MM -MT $(@:.d=.o) >$@


.PHONY: clean
clean:
	$(RM) $(OBJS) $(DYLIBTARGET) $(LIBTARGET)

.PHONY: cleandep
cleandep: clean
	$(RM) $(DEPS)


.PHONY: install
install: build
	mkdir -p ${PREFIX}/idris2-${IDRIS2_VERSION}/lib
	mkdir -p ${PREFIX}/idris2-${IDRIS2_VERSION}/support/c
	install -m 755 $(DYLIBTARGET) ${PREFIX}/idris2-${IDRIS2_VERSION}/lib
	install -m 644 $(LIBTARGET)   ${PREFIX}/idris2-${IDRIS2_VERSION}/lib
	install -m 644 *.h            ${PREFIX}/idris2-${IDRIS2_VERSION}/support/c
