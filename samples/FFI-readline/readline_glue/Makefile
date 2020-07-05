include ../../../config.mk

IDRIS := idris2
INSTALLDIR = `${IDRIS} --libdir`/readline/lib

TARGET = libidrisreadline

LDFLAGS += -lreadline

SRCS = $(wildcard *.c)
OBJS = $(SRCS:.c=.o)
DEPS = $(OBJS:.o=.d)


all: $(TARGET)$(SHLIB_SUFFIX)

$(TARGET)$(SHLIB_SUFFIX): $(OBJS)
	$(CC) -shared $(LDFLAGS) -o $@ $^


-include $(DEPS)

%.d: %.c
	@$(CPP) $(CFLAGS) $< -MM -MT $(@:.d=.o) >$@


.PHONY: clean

clean :
	rm -f $(OBJS) $(TARGET)$(SHLIB_SUFFIX)

cleandep: clean
	rm -f $(DEPS)


.PHONY: install

install:
	@if ! [ -d $(INSTALLDIR) ]; then mkdir -p $(INSTALLDIR); fi
	install $(TARGET)$(SHLIB_SUFFIX) $(wildcard *.h) $(INSTALLDIR)
