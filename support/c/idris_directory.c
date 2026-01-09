#include "idris_directory.h"
#include "idris_support.h"

#include <dirent.h>
#include <errno.h>
#include <pthread.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/stat.h>
#include <sys/types.h>
#include <unistd.h>

#include "idris_util.h"

char *idris2_currentDirectory() {
  char *cwd = malloc(1024); // probably ought to deal with the unlikely event of
                            // this being too small
  IDRIS2_VERIFY(cwd, "malloc failed");
  return getcwd(cwd, 1024); // Freed by RTS
}

int idris2_changeDir(char *dir) { return chdir(dir); }

int idris2_createDir(char *dir) {
#ifdef _WIN32
  return mkdir(dir);
#else
  return mkdir(dir, S_IRWXU | S_IRWXG | S_IRWXO);
#endif
}

typedef struct {
  DIR *dirptr;
  // Attempt to fix failed to list XXX: Cannot allocate memory
  // readdir_r is deprecated, so, we should use a mutex
  pthread_mutex_t mutex;
} DirInfo;

void *idris2_openDir(char *dir) {
  DIR *d = opendir(dir);
  if (d == NULL) {
    return NULL;
  } else {
    DirInfo *di = malloc(sizeof(DirInfo));
    IDRIS2_VERIFY(di, "malloc failed");
    di->dirptr = d;

    if (pthread_mutex_init(&di->mutex, NULL) != 0) {
      closedir(d);
      free(di);
      IDRIS2_VERIFY(0, "idris2_openDir mutex init failed");
      return NULL;
    }

    return (void *)di;
  }
}

void idris2_closeDir(void *d) {
  DirInfo *di = (DirInfo *)d;

  pthread_mutex_destroy(&di->mutex);

  IDRIS2_VERIFY(closedir(di->dirptr) == 0, "closedir failed: %s",
                strerror(errno));
  free(di);
}

int idris2_removeDir(char *path) { return rmdir(path); }

char *idris2_nextDirEntry(void *d) {
  DirInfo *di = (DirInfo *)d;

  // Going to avoid the usage of pthread_mutex_lock(&di->mutex);
  // to prevent silent deadlocks

  int rc;
  unsigned int attempts = 0;

  while ((rc = pthread_mutex_trylock(&di->mutex)) == EBUSY) {
    attempts++;

    if (attempts % 100 == 0) {
      fprintf(stderr, "idris2_nextDirEntry: Still waiting for mutex (%u)\n",
              attempts);
    }

    idris2_usleep(10000);
  }

  IDRIS2_VERIFY(rc == 0, "idris2_nextDirEntry: Unexpected mutex error: %s",
                strerror(rc));

  // `readdir` keeps `errno` unchanged on end of stream
  // so we need to reset `errno` to distinguish between
  // end of stream and failure.
  errno = 0;
  struct dirent *de = readdir(di->dirptr);

  pthread_mutex_unlock(&di->mutex);

  if (de == NULL) {
    return NULL;
  } else {
    return de->d_name;
  }
}
