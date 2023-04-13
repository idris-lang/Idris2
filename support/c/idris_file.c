#include "idris_file.h"
#include "getline.h"

#include <dirent.h>
#include <errno.h>
#include <fcntl.h>
#include <string.h>
#include <sys/time.h>
#include <time.h>
#include <unistd.h>

#ifdef _WIN32
#include "windows/win_utils.h"
#include <windows.h>
#else
#include <sys/select.h>
#include <sys/wait.h>
#endif

#include "idris_util.h"

FILE *idris2_openFile(char *name, char *mode) {
#ifdef _WIN32
  FILE *f = win32_u8fopen(name, mode);
#else
  FILE *f = fopen(name, mode);
#endif
  return (void *)f;
}

void idris2_closeFile(FILE *f) {
  IDRIS2_VERIFY(fclose(f) == 0, "fclose failed: %s", strerror(errno));
}

int idris2_getFileNo(FILE *f) {
#ifdef _WIN32
  return win32_getFileNo(f);
#else
  return fileno(f);
#endif
}

int idris2_fileError(FILE *f) { return ferror(f); }

int idris2_fileErrno() {
  switch (errno) {
  case ENOENT:
    return 2;
  case EACCES:
    return 3;
  case EEXIST:
    return 4;
  default:
    return (errno + 5);
  }
}

int idris2_chmod(const char *path, mode_t mode) {
#ifdef _WIN32
  // return _chmod(path, mode);
  return 0; /* ??? (from win_hack.c) */
#else
  return chmod(path, mode);
#endif
}

int idris2_removeFile(const char *filename) { return remove(filename); }

int idris2_fileSize(FILE *f) {
  int fd = idris2_getFileNo(f);

  struct stat buf;
  if (fstat(fd, &buf) == 0) {
    return (int)(buf.st_size);
  } else {
    return -1;
  }
}

int idris2_fpoll(FILE *f) {
#ifdef _WIN32
  return win_fpoll(f);
#else
  fd_set x;
  struct timeval timeout;
  timeout.tv_sec = 1;
  timeout.tv_usec = 0;
  int fd = idris2_getFileNo(f);

  FD_ZERO(&x);
  FD_SET(fd, &x);

  int r = select(fd + 1, &x, 0, 0, &timeout);
  return r;
#endif
}

void *idris2_popen(const char *cmd, const char *mode) {
#ifdef _WIN32
  FILE *f = win32_u8popen(cmd, mode);
#else
  FILE *f = popen(cmd, mode);
#endif
  return f;
}

int idris2_pclose(void *stream) {
#ifdef _WIN32
  int r = _pclose(stream);
  IDRIS2_VERIFY(r != -1, "pclose failed");
  return r;
#else
  int r = pclose(stream);
  IDRIS2_VERIFY(WIFEXITED(r), "pclose failed");
  return WEXITSTATUS(r);
#endif
}

// seek through the next newline, consuming and
// throwing away anything until then.
int idris2_seekLine(FILE *f) {
  while (1) {
    int c = fgetc(f);
    if (c == -1) {
      if (feof(f)) {
        return 0;
      } else {
        return -1;
      }
    }
    if (c == '\n') {
      return 0;
    }
  }
}

char *idris2_readLine(FILE *f) {
  char *buffer = NULL;
  size_t n = 0;
  ssize_t len;
  len = getline(&buffer, &n, f);
  if (len < 0 && buffer != NULL) {
    buffer[0] = '\0'; // Copy Idris 1 behaviour - empty string if nothing read
  }
  return buffer; // freed by RTS if not NULL
}

char *idris2_readChars(int num, FILE *f) {
  char *buffer = malloc((num + 1) * sizeof(char));
  size_t len;
  len = fread(buffer, sizeof(char), (size_t)num, f);
  buffer[len] = '\0';

  if (len <= 0) {
    return NULL;
  } else {
    return buffer; // freed by RTS
  }
}

size_t idris2_readBufferData(FILE *h, char *buffer, size_t loc, size_t max) {
  return fread(buffer + loc, sizeof(uint8_t), max, h);
}

int idris2_writeLine(FILE *f, char *str) {
  if (fputs(str, f) == EOF) {
    return 0;
  } else {
    return 1;
  }
}

size_t idris2_writeBufferData(FILE *h, const char *buffer, size_t loc,
                              size_t len) {
  return fwrite(buffer + loc, sizeof(uint8_t), len, h);
}

int idris2_eof(FILE *f) { return feof(f); }

int idris2_fileAccessTime(FILE *f) {
  int fd = idris2_getFileNo(f);

  struct stat buf;
  if (fstat(fd, &buf) == 0) {
    return buf.st_atime;
  } else {
    return -1;
  }
}

int idris2_fileModifiedTime(FILE *f) {
  int fd = idris2_getFileNo(f);

  struct stat buf;
  if (fstat(fd, &buf) == 0) {
    return buf.st_mtime;
  } else {
    return -1;
  }
}

int idris2_fileStatusTime(FILE *f) {
  int fd = idris2_getFileNo(f);

  struct stat buf;
  if (fstat(fd, &buf) == 0) {
    return buf.st_ctime;
  } else {
    return -1;
  }
}

int idris2_fileIsTTY(FILE *f) {
  int fd = idris2_getFileNo(f);
#ifdef _WIN32
  return win32_isTTY(fd);
#else
  return isatty(fd);
#endif
}

FILE *idris2_stdin() { return stdin; }

FILE *idris2_stdout() { return stdout; }

FILE *idris2_stderr() { return stderr; }

struct child_process {
  pid_t pid;
  FILE *in;
  FILE *out;
};

// Open a bi-directional pipe, returning the above structure
// with pid and two file handles.
struct child_process *idris2_popen2(char *cmd) {
#ifdef _WIN32
  SECURITY_ATTRIBUTES saAttr;
  HANDLE pipes[4];
  STARTUPINFO si;
  PROCESS_INFORMATION pi;
  ZeroMemory(&pi, sizeof(PROCESS_INFORMATION));

  saAttr.nLength = sizeof(SECURITY_ATTRIBUTES);
  saAttr.bInheritHandle = TRUE;
  saAttr.lpSecurityDescriptor = NULL;

  if (!CreatePipe(&pipes[0], &pipes[1], &saAttr, 0) ||
      !CreatePipe(&pipes[2], &pipes[3], &saAttr, 0)) {
    return NULL;
  }
  char cmdline[4096];
  int len = snprintf(cmdline, 4096, "cmd /c %s", cmd);
  if (len > 4095 || len < 0) {
    return NULL;
  }
  ZeroMemory(&si, sizeof(si));
  si.cb = sizeof(si);
  si.hStdInput = pipes[2];
  si.hStdOutput = pipes[1];
  // si.hStdError = pipes[1];
  si.dwFlags |= STARTF_USESTDHANDLES;
  SetHandleInformation(pipes[3], HANDLE_FLAG_INHERIT, 0);
  SetHandleInformation(pipes[0], HANDLE_FLAG_INHERIT, 0);
  if (!CreateProcess(NULL, cmdline, NULL, NULL, TRUE, 0, NULL, NULL, &si,
                     &pi)) {
    return NULL;
  }
  struct child_process *rval = malloc(sizeof(struct child_process));
  int in_fd = _open_osfhandle((intptr_t)pipes[3], _O_WRONLY);
  int out_fd = _open_osfhandle((intptr_t)pipes[0], _O_RDONLY);
  CloseHandle(pipes[1]);
  CloseHandle(pipes[2]);
  CloseHandle(pi.hProcess);
  CloseHandle(pi.hThread);
  rval->in = _fdopen(in_fd, "w");
  rval->out = _fdopen(out_fd, "r");
  rval->pid = pi.dwProcessId;
  return rval;
#else
  int pipes[4];
  int err = 0;
  err = pipe(&pipes[0]);
  if (err) {
    return NULL;
  }

  err = pipe(&pipes[2]);
  if (err) {
    close(pipes[0]);
    close(pipes[1]);
    return NULL;
  }
  pid_t pid = fork();
  if (pid < 0) {
    perror("fork");
    return NULL;
  } else if (pid > 0) {
    struct child_process *rval = malloc(sizeof(struct child_process));
    close(pipes[1]);
    close(pipes[2]);
    rval->in = fdopen(pipes[3], "w");
    rval->out = fdopen(pipes[0], "r");
    rval->pid = pid;
    return rval;
  } else {
    close(STDOUT_FILENO);
    dup2(pipes[1], STDOUT_FILENO);
    close(pipes[0]);
    close(pipes[1]);

    close(STDIN_FILENO);
    dup2(pipes[2], STDIN_FILENO);
    close(pipes[2]);
    close(pipes[3]);

    err = execlp("/bin/sh", "sh", "-c", cmd, NULL);
    // We only reach this point if there is an error.
    // Maybe report something to stderr so the user knows what's up?
    perror("execl");
    exit(err);
  }
#endif
}

int idris2_popen2ChildPid(struct child_process *ptr) {
  if (!ptr)
    return 0;
  return ptr->pid;
}

FILE *idris2_popen2FileIn(struct child_process *ptr) {
  if (!ptr)
    return NULL;
  return ptr->in;
}

FILE *idris2_popen2FileOut(struct child_process *ptr) {
  if (!ptr)
    return NULL;
  return ptr->out;
}
