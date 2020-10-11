include ../../config.mk

TARGET = libidris2_refc

LIBTARGET = $(TARGET).a

CFLAGS += -O2

SRCS = $(wildcard *.c)
ifeq ($(OS), windows)
	SRCS += windows/win_utils.c windows/win_hack.c
	LDFLAGS += -lws2_32
ifeq ($(OLD_WIN), 1)
	CFLAGS += -D_OLD_WIN
endif
endif
OBJS = $(SRCS:.c=.o)
DEPS = $(OBJS:.o=.d)


all: build

.PHONY: build

build: $(LIBTARGET)

$(LIBTARGET): $(OBJS)
	$(AR) rc $@ $^
	$(RANLIB) $@

-include $(DEPS)

%.d: %.c
	@$(CPP) $(CFLAGS) $< -MM -MT $(@:.d=.o) >$@


.PHONY: clean

clean:
	$(RM) $(OBJS) $(LIBTARGET)

cleandep: clean
	$(RM) $(DEPS)


.PHONY: install

install: build
	mkdir -p ${PREFIX}/idris2-${IDRIS2_VERSION}/refc
	install $(LIBTARGET) *.h ${PREFIX}/idris2-${IDRIS2_VERSION}/refc
