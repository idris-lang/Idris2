#include "idris_support.h"
#include "idris_file.h"

#include <errno.h>
#include <stdio.h>
#include <string.h>
#include <time.h>
#include <stdlib.h>
#include <unistd.h>

int _argc;
char **_argv;

#ifdef _WIN32
extern char **_environ;
#include "windows/win_utils.h"
#define environ _environ
#else
extern char** environ;
#endif

int idris2_isNull(void* ptr) {
    return (ptr == NULL);
}

void *idris2_getNull() {
    return NULL;
}

char* idris2_getString(void *p) {
    return (char*)p;
}

int idris2_getErrno() {
#ifdef _WIN32
    return win32_getErrno();
#else
    return errno;
#endif
}

char* idris2_getStr() {
    char *inp = idris2_readLine(stdin);
    // Remove trailing newline; easier to do this than in PrimIO which
    // doesn't have the relevant functions available yet
    for(char *c = inp; *c != '\0'; ++c) {
        if (*c == '\n' || *c == '\r') {
            *c = '\0';
        }
    }
    return inp;
}

void idris2_putStr(char* f) {
    idris2_writeLine(stdout, f);
}

#ifndef _WIN32
static void idris2_nanosleep(time_t seconds, long nanos) {
    struct timespec t;
    t.tv_sec = seconds;
    t.tv_nsec = nanos;
    for (;;) {
        int r = nanosleep(&t, &t);
        if (r == 0) {
            return;
        }
        if (errno == EINTR) {
            continue;
        }
        fprintf(stderr, "nanosleep failed: %s\n", strerror(errno));
        abort();
    }
}
#endif

void idris2_sleep(int sec) {
    if (sec <= 0) {
        return;
    }
#ifdef _WIN32
    win32_sleep(sec*1000);
#else
    idris2_nanosleep(sec, 0);
#endif
}

void idris2_usleep(int usec) {
    if (usec <= 0) {
        return;
    }
#ifdef _WIN32
    win32_sleep(usec/1000);
#else
    idris2_nanosleep(usec / 1000000, usec % 1000000 * 1000);
#endif
}

int idris2_time() {
    return time(NULL); // RTS needs to have 32 bit integers at least
}

void idris2_setArgs(int argc, char *argv[]) {
    _argc = argc;
    _argv = argv;
}

int idris2_getArgCount() {
    return _argc;
}

char* idris2_getArg(int n) {
    return _argv[n];
}

char* idris2_getEnvPair(int i) {
    return *(environ + i);
}

int idris2_setenv(const char *name, const char *value, int overwrite) {
#ifdef _WIN32
    return win32_modenv(name, value, overwrite);
#else
    return setenv(name, value, overwrite);
#endif
}

int idris2_unsetenv(const char *name) {
#ifdef _WIN32
    return win32_modenv(name, "", 1);
#else
    return unsetenv(name);
#endif
}

int idris2_getPID() {
#ifdef _WIN32
    return win32_getPID();
#else
    return getpid();
#endif
}

// get the number of processors configured
long idris2_getNProcessors() {
#ifdef _WIN32
    return win32_getNProcessors();
#else
    return sysconf(_SC_NPROCESSORS_CONF);
#endif
}

