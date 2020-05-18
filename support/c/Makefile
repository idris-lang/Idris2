include $(IDRIS2_CURDIR)/config.mk

TARGET = libidris2_support

LIBTARGET = $(TARGET).a
DYLIBTARGET = $(TARGET)$(SHLIB_SUFFIX)

CFLAGS += -O2

SRCS = $(wildcard *.c)
OBJS = $(SRCS:.c=.o)
DEPS = $(OBJS:.o=.d)


all: build

.PHONY: build

build: $(LIBTARGET) $(DYLIBTARGET)

$(LIBTARGET): $(OBJS)
	$(AR) rc $@ $^
	$(RANLIB) $@

$(DYLIBTARGET): $(OBJS)
	$(CC) -shared $(LDFLAGS) -o $@ $^


-include $(DEPS)

%.d: %.c
	@$(CPP) $(CFLAGS) $< -MM -MT $(@:.d=.o) >$@


.PHONY: clean

clean:
	rm -f $(OBJS) $(DYLIBTARGET) $(LIBTARGET)

cleandep: clean
	rm -f $(DEPS)


.PHONY: install

install: build
	mkdir -p ${PREFIX}/idris2-${IDRIS2_VERSION}/lib
	install $(LIBTARGET) $(DYLIBTARGET) ${PREFIX}/idris2-${IDRIS2_VERSION}/lib
