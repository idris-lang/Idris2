#ifndef __IDRIS_DIRECTORY_H
#define __IDRIS_DIRECTORY_H

char* idris2_currentDirectory();
int idris2_changeDir(char* dir);
int idris2_createDir(char* dir);
void* idris2_dirOpen(char* dir);
void idris2_dirClose(void* d);
char* idris2_nextDirEntry(void* d);

#endif
