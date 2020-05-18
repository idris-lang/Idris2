#ifndef __IDRIS_FILE_H
#define __IDRIS_FILE_H

#include <stdio.h>

FILE* idris2_openFile(char* name, char* mode);
void idris2_closeFile(FILE* f);

int idris2_fileError(FILE* f);

// Turn errno into an integer understandable by System.File
int idris2_fileErrno();

int idris2_fileRemove(const char *filename);
int idris2_fileSize(FILE* h);

int idris2_fpoll(FILE* f);

// Treat as a Ptr String (might be NULL)
char* idris2_readLine(FILE* f);
char* idris_readChars(int num, FILE* f);

int idris2_writeLine(FILE* f, char* str);

int idris2_eof(FILE* f);
int idris2_fileAccessTime(FILE* f);
int idris2_fileModifiedTime(FILE* f);
int idris2_fileStatusTime(FILE* f);

FILE* idris2_stdin();
FILE* idris2_stdout();
FILE* idris2_stderr();

#endif
