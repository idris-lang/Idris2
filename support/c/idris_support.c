#include "idris_support.h"
#include "idris_file.h"

#include <errno.h>
#include <stdio.h>
#include <string.h>
#include <time.h>

extern char** environ;

int idris2_isNull(void* ptr) {
    return (ptr == NULL);
}

char* idris2_getString(void *p) {
    return (char*)p;
}

int idris2_getErrno() {
    return errno;
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

void idris2_sleep(int sec) {
    struct timespec t;
    t.tv_sec = sec;
    t.tv_nsec = 0;

    nanosleep(&t, NULL);
}

void idris2_usleep(int usec) {
    struct timespec t;
    t.tv_sec = usec / 1000000;
    t.tv_nsec = (usec % 1000000) * 1000;

    nanosleep(&t, NULL);
}

int idris2_time() {
    return time(NULL); // RTS needs to have 32 bit integers at least
}

char* idris2_getEnvPair(int i) {
    return *(environ + i);
}
