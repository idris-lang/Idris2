include ../../common.mk

TARGET = libidris2_refc

LIBTARGET = $(TARGET).a

SRCS := $(wildcard *.c)
OBJS = $(SRCS:.c=.o)
DEPS = $(OBJS:.o=.d)

CFLAGS += -O2

ifeq ($(OLD_WIN), 1)
	CPPFLAGS += -D_OLD_WIN
endif


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
	mkdir -p "$(PREFIX)/$(IDRIS_INSTALL_DIR)/support/refc"
	install -m 644 $(LIBTARGET) *.h "$(PREFIX)/$(IDRIS_INSTALL_DIR)/support/refc"
