include ../../config.mk

INSTALLDIR = ${PREFIX}/idris2-${IDRIS2_VERSION}/network/lib

IDRIS_SRCS = Network/Socket.idr Network/Socket/Data.idr Network/Socket/Raw.idr

TARGET = idris_net

SRCS = idris_net.c
OBJS = $(SRCS:.c=.o)
DEPS = $(OBJS:.o=.d)

ifeq ($(OS), windows)
	LDFLAGS += -lws2_32
endif


all: $(TARGET)$(SHLIB_SUFFIX)
	${IDRIS2} --build network.ipkg


build: $(TARGET)$(SHLIB_SUFFIX) $(IDRIS_SRCS)
	@if [ -z "${IDRIS2}" ]; then echo 'variable $$IDRIS2 is not set, aborting'; exit 1; fi
	${IDRIS2} --build network.ipkg

$(TARGET)$(SHLIB_SUFFIX): $(OBJS)
	$(CC) -shared  -o $@ $^ $(LDFLAGS)


-include $(DEPS)

%.d: %.c
	@$(CPP) $(CFLAGS) $< -MM -MT $(@:.d=.o) >$@


.PHONY: clean

clean :
	$(RM) $(OBJS) $(TARGET)$(SHLIB_SUFFIX)
	$(RM) -r build

cleandep: clean
	$(RM) $(DEPS)


.PHONY: install

install:
	@if [ -z "${IDRIS2}" ]; then echo 'variable $$IDRIS2 is not set, aborting'; exit 1; fi
	${IDRIS2} --install network.ipkg
	@if ! [ -d $(INSTALLDIR) ]; then mkdir -p $(INSTALLDIR); fi
	install $(TARGET)$(SHLIB_SUFFIX) $(wildcard *.h) $(INSTALLDIR)


test: build test.c
	$(CC) -o network-tests -L. -I. test.c $(TARGET)$(SHLIB_SUFFIX)
	LD_LIBRARY_PATH=. ./network-tests
	@$(RM) ./network-tests test.o
