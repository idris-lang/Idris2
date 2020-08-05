include ../../../config.mk

TARGET = libmkalloc

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
	$(RM) $(OBJS) $(TARGET)$(SHLIB_SUFFIX)

cleandep: clean
	$(RM) $(DEPS)
