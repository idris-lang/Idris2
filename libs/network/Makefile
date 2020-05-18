include $(IDRIS2_CURDIR)/config.mk

INSTALLDIR = `${IDRIS2} --libdir`/network/lib

IDRIS_SRCS = Network/Socket.idr Network/Socket/Data.idr Network/Socket/Raw.idr

TARGET = idris_net

SRCS = $(wildcard *.c)
OBJS = $(SRCS:.c=.o)
DEPS = $(OBJS:.o=.d)


all: $(TARGET)$(SHLIB_SUFFIX)
	${IDRIS2} --build network.ipkg


build: $(TARGET)$(SHLIB_SUFFIX) $(IDRIS_SRCS)
	@if [ -z "${IDRIS2}" ]; then echo 'variable $$IDRIS2 is not set, aborting'; exit 1; fi
	${IDRIS2} --build network.ipkg

$(TARGET)$(SHLIB_SUFFIX): $(OBJS)
	$(CC) -shared $(LDFLAGS) -o $@ $^


-include $(DEPS)

%.d: %.c
	@$(CPP) $(CFLAGS) $< -MM -MT $(@:.d=.o) >$@


.PHONY: clean

clean :
	rm -f $(OBJS) $(TARGET)$(SHLIB_SUFFIX)
	rm -rf build

cleandep: clean
	rm -f $(DEPS)


.PHONY: install

install:
	@if [ -z "${IDRIS2}" ]; then echo 'variable $$IDRIS2 is not set, aborting'; exit 1; fi
	${IDRIS2} --install network.ipkg
	@if ! [ -d $(INSTALLDIR) ]; then mkdir -p $(INSTALLDIR); fi
	install $(TARGET)$(SHLIB_SUFFIX) $(wildcard *.h) $(INSTALLDIR)


test: build test.c
	$(CC) -o network-tests -L. -I. test.c $(TARGET)$(SHLIB_SUFFIX)
	LD_LIBRARY_PATH=. ./network-tests
	@rm -f ./network-tests test.o
