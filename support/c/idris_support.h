#ifndef __IDRIS_SUPPORT_H
#define __IDRIS_SUPPORT_H

// Return non-zero if the pointer is null
int idris2_isNull(void*);
// Returns a NULL
void *idris2_getNull();
// Convert a Ptr String intro a String, assuming the string has been checked
// to be non-null
char* idris2_getString(void *p);
int idris2_getErrno();

char* idris2_getStr();
void idris2_putStr(char* f);

void idris2_sleep(int sec);
void idris2_usleep(int usec);
int idris2_time();

char* idris2_getEnvPair(int i);

long idris2_getNProcessors();

#endif
