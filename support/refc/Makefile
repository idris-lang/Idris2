include ../../config.mk

TARGET = libidris2_refc

LIBTARGET = $(TARGET).a

SRCS := $(wildcard *.c)
OBJS = $(SRCS:.c=.o)
DEPS = $(OBJS:.o=.d)

CFLAGS += -O2

ifeq ($(OLD_WIN), 1)
	CPPFLAGS += -D_OLD_WIN
endif


.PHONY: all
all: build

.PHONY: build
build: $(LIBTARGET)

$(LIBTARGET): $(OBJS)
	$(AR) rc $@ $^
	$(RANLIB) $@

-include $(DEPS)

%.d: %.c
	@$(CPP) $(CPPFLAGS) $< -MM -MT $(@:.d=.o) >$@


.PHONY: clean
clean:
	$(RM) $(OBJS) $(LIBTARGET)

.PHONY: cleandep
cleandep: clean
	$(RM) $(DEPS)


.PHONY: check-warnings
check-warnings:
	$(CC) $(CPPFLAGS) -Wall -Wextra -Wstrict-prototypes -Wpedantic \
	      -fsyntax-only $(SRCS)

.PHONY: test-asan
test-asan:
	$(MAKE) clean
	$(MAKE) build CFLAGS="$(CFLAGS) -fsanitize=address,undefined -fno-omit-frame-pointer -g"

.PHONY: test-tsan
test-tsan:
	$(MAKE) clean
	$(MAKE) build CFLAGS="$(CFLAGS) -fsanitize=thread -fno-omit-frame-pointer -g"

.PHONY: install
install: build
	mkdir -p ${DESTDIR}${PREFIX}/idris2-${IDRIS2_VERSION}/support/refc
	install -m 644 $(LIBTARGET) *.h ${DESTDIR}${PREFIX}/idris2-${IDRIS2_VERSION}/support/refc
