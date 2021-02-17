include ../../config.mk

TARGET = libidris2_refc

LIBTARGET = $(TARGET).a
IDRIS2_DESTDIR := ${DESTDIR}${PREFIX}

CFLAGS += -O2

SRCS = $(wildcard *.c)
ifeq ($(OS), windows)
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
	mkdir -p ${IDRIS2_DESTDIR}/idris2-${IDRIS2_VERSION}/refc
	install $(LIBTARGET) *.h ${IDRIS2_DESTDIR}/idris2-${IDRIS2_VERSION}/refc
