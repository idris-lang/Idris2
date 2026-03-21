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

# Build variants for embedded/bare-metal targets.
# IDRIS2_NO_GMP: replace GMP Integer with int64_t (no -lgmp needed)
# IDRIS2_NO_THREADS: stub out all pthread usage (no -lpthread needed)
# IDRIS2_NO_STDIO: exclude fprintf/vsnprintf (override IDRIS2_WRITE_STDERR for UART output)
# IDRIS2_NO_CLOCK: stub time()/clock() to return 0
.PHONY: build-no-gmp
build-no-gmp:
	$(MAKE) clean
	$(MAKE) build CPPFLAGS="$(CPPFLAGS) -DIDRIS2_NO_GMP"

.PHONY: build-no-threads
build-no-threads:
	$(MAKE) clean
	$(MAKE) build CPPFLAGS="$(CPPFLAGS) -DIDRIS2_NO_THREADS"

.PHONY: build-embedded
build-embedded:
	$(MAKE) clean
	$(MAKE) build CPPFLAGS="$(CPPFLAGS) -DIDRIS2_NO_GMP -DIDRIS2_NO_THREADS -DIDRIS2_NO_STDIO -DIDRIS2_NO_CLOCK"

# Cross-compiler for ARM bare-metal (defaults to arm-none-eabi-gcc if found).
CROSS_CC ?= arm-none-eabi-gcc
CROSS_AR ?= arm-none-eabi-ar
CROSS_RANLIB ?= arm-none-eabi-ranlib
EMBEDDED_CPPFLAGS := -DIDRIS2_NO_GMP -DIDRIS2_NO_THREADS -DIDRIS2_NO_STDIO -DIDRIS2_NO_CLOCK

# ARM Cortex-M4 (STM32F4xx, STM32L4xx, etc.)
.PHONY: build-arm-cm4
build-arm-cm4:
	mkdir -p build/arm-cm4
	for s in $(SRCS); do \
	  $(CROSS_CC) $(EMBEDDED_CPPFLAGS) \
	    -mcpu=cortex-m4 -mthumb -mfloat-abi=hard -mfpu=fpv4-sp-d16 \
	    -O2 -I. -c $$s -o build/arm-cm4/$${s%.c}.o || exit 1; \
	done
	$(CROSS_AR) rc build/arm-cm4/libidris2_refc.a build/arm-cm4/*.o
	$(CROSS_RANLIB) build/arm-cm4/libidris2_refc.a

# ARM Cortex-M0+ (STM32G0xx, STM32L0xx, etc.)
.PHONY: build-arm-cm0plus
build-arm-cm0plus:
	mkdir -p build/arm-cm0plus
	for s in $(SRCS); do \
	  $(CROSS_CC) $(EMBEDDED_CPPFLAGS) \
	    -mcpu=cortex-m0plus -mthumb \
	    -O2 -I. -c $$s -o build/arm-cm0plus/$${s%.c}.o || exit 1; \
	done
	$(CROSS_AR) rc build/arm-cm0plus/libidris2_refc.a build/arm-cm0plus/*.o
	$(CROSS_RANLIB) build/arm-cm0plus/libidris2_refc.a

# ARM Cortex-M33 (STM32U5xx, STM32H5xx, etc.)
.PHONY: build-arm-cm33
build-arm-cm33:
	mkdir -p build/arm-cm33
	for s in $(SRCS); do \
	  $(CROSS_CC) $(EMBEDDED_CPPFLAGS) \
	    -mcpu=cortex-m33 -mthumb -mfloat-abi=hard -mfpu=fpv5-sp-d16 \
	    -O2 -I. -c $$s -o build/arm-cm33/$${s%.c}.o || exit 1; \
	done
	$(CROSS_AR) rc build/arm-cm33/libidris2_refc.a build/arm-cm33/*.o
	$(CROSS_RANLIB) build/arm-cm33/libidris2_refc.a

CROSS_INSTALL_DIR ?= /usr/local/arm-none-eabi

.PHONY: install-arm-cm4
install-arm-cm4: build-arm-cm4
	mkdir -p $(CROSS_INSTALL_DIR)/lib $(CROSS_INSTALL_DIR)/include/idris2_refc
	install -m 644 build/arm-cm4/libidris2_refc.a $(CROSS_INSTALL_DIR)/lib/
	install -m 644 *.h $(CROSS_INSTALL_DIR)/include/idris2_refc/

.PHONY: install-arm-cm0plus
install-arm-cm0plus: build-arm-cm0plus
	mkdir -p $(CROSS_INSTALL_DIR)/lib $(CROSS_INSTALL_DIR)/include/idris2_refc
	install -m 644 build/arm-cm0plus/libidris2_refc.a $(CROSS_INSTALL_DIR)/lib/
	install -m 644 *.h $(CROSS_INSTALL_DIR)/include/idris2_refc/

.PHONY: install-arm-cm33
install-arm-cm33: build-arm-cm33
	mkdir -p $(CROSS_INSTALL_DIR)/lib $(CROSS_INSTALL_DIR)/include/idris2_refc
	install -m 644 build/arm-cm33/libidris2_refc.a $(CROSS_INSTALL_DIR)/lib/
	install -m 644 *.h $(CROSS_INSTALL_DIR)/include/idris2_refc/

.PHONY: install
install: build
	mkdir -p ${DESTDIR}${PREFIX}/idris2-${IDRIS2_VERSION}/support/refc
	install -m 644 $(LIBTARGET) *.h ${DESTDIR}${PREFIX}/idris2-${IDRIS2_VERSION}/support/refc
