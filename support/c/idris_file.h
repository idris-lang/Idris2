#pragma once

#include <stdint.h>
#include <stdio.h>
#include <sys/stat.h>
#include <sys/types.h>

#ifdef _WIN32
#include <io.h>
#include <processthreadsapi.h>
#endif

FILE *idris2_openFile(char *name, char *mode);
void idris2_closeFile(FILE *f);

int idris2_fileError(FILE *f);

// Turn errno into an integer understandable by System.File
int idris2_fileErrno();

int idris2_chmod(const char *path, mode_t mode);
int idris2_removeFile(const char *filename);
int idris2_fileSize(FILE *h);

int idris2_fpoll(FILE *f);

void *idris2_popen(const char *cmd, const char *mode);
int idris2_pclose(void *stream);

// Seek through the next newline without
// saving anything along the way
int idris2_seekLine(FILE *f);

// Treat as a Ptr String (might be NULL)
char *idris2_readLine(FILE *f);
char *idris2_readChars(int num, FILE *f);
size_t idris2_readBufferData(FILE *h, char *buffer, size_t loc, size_t max);

int idris2_writeLine(FILE *f, char *str);
size_t idris2_writeBufferData(FILE *h, const char *buffer, size_t loc,
                              size_t len);

int idris2_eof(FILE *f);

struct filetime;

struct filetime *idris2_fileTime(FILE *f);
int idris2_fileModifiedTime(FILE *f);

int idris2_filetimeAccessTimeSec(struct filetime *f);
int idris2_filetimeAccessTimeNsec(struct filetime *f);
int idris2_filetimeModifiedTimeSec(struct filetime *f);
int idris2_filetimeModifiedTimeNsec(struct filetime *f);
int idris2_filetimeStatusTimeSec(struct filetime *f);
int idris2_filetimeStatusTimeNsec(struct filetime *f);

FILE *idris2_stdin();
FILE *idris2_stdout();
FILE *idris2_stderr();

struct child_process;

struct child_process *idris2_popen2(char *cmd);

int idris2_popen2ChildPid(struct child_process *ptr);
void *idris2_popen2ChildHandler(struct child_process *ptr);
FILE *idris2_popen2FileIn(struct child_process *ptr);
FILE *idris2_popen2FileOut(struct child_process *ptr);

int idris2_popen2WaitByHandler(void *hProcess);
int idris2_popen2WaitByPid(pid_t pid);
