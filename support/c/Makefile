include ../../config.mk

TARGET = libidris2_support

LIBTARGET = $(TARGET).a
DYLIBTARGET = $(TARGET)$(SHLIB_SUFFIX)

CFLAGS += -O2

SRCS = $(wildcard *.c)
ifeq ($(OS), windows)
	SRCS += windows/win_utils.c windows/win_hack.c
	LDFLAGS += -lws2_32
endif
OBJS = $(SRCS:.c=.o)
DEPS = $(OBJS:.o=.d)


all: build

.PHONY: build

build: $(LIBTARGET) $(DYLIBTARGET)

$(LIBTARGET): $(OBJS)
	$(AR) rc $@ $^
	$(RANLIB) $@

$(DYLIBTARGET): $(OBJS)
	$(CC) -shared -o $@ $^ $(LDFLAGS)


-include $(DEPS)

%.d: %.c
	@$(CPP) $(CFLAGS) $< -MM -MT $(@:.d=.o) >$@


.PHONY: clean

clean:
	$(RM) $(OBJS) $(DYLIBTARGET) $(LIBTARGET)

cleandep: clean
	$(RM) $(DEPS)


.PHONY: install

install: build
	mkdir -p ${PREFIX}/idris2-${IDRIS2_VERSION}/lib
	install $(LIBTARGET) $(DYLIBTARGET) ${PREFIX}/idris2-${IDRIS2_VERSION}/lib
