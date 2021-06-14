#include "idris_signal.h"

#include <stdlib.h>
#include <stdio.h>
#include <signal.h>

#ifdef _WIN32
#include <windows.h>
HANDLE ghMutex;
#else
#include <pthread.h>
static pthread_mutex_t sig_mutex = PTHREAD_MUTEX_INITIALIZER;
#endif

// ring buffer style storage for collected
// signals.
static int signal_buf_cap = 0;
static int signals_in_buf = 0;
static int signal_buf_next_read_idx = 0;
static int *signal_buf = NULL;

void _init_buf() {
  if (signal_buf == NULL) {
    signal_buf_cap = 10;
    signal_buf = malloc(sizeof(int) * signal_buf_cap);
  }
}

// returns truthy or falsey (1 or 0)
int _lock() {
#ifdef _WIN32
  if (ghMutex == NULL) {
    ghMutex = CreateMutex(
      NULL,
      FALSE,
      NULL);
  }

  DWORD dwWaitResult = WaitForSingleObject(
    ghMutex,
    INFINITE);

  switch (dwWaitResult) 
    {
       case WAIT_OBJECT_0: 
         return 1;

       case WAIT_ABANDONED: 
         return 0;
    }
#else
  pthread_mutex_lock(&sig_mutex);
  return 1;
#endif
}

void _unlock() {
#ifdef _WIN32
  ReleaseMutex(ghMutex);
#else
  pthread_mutex_unlock(&sig_mutex);
#endif
}

void _collect_signal(int signum);

void _collect_signal_core(int signum) {
  _init_buf();

  // FIXME: allow for adjusting capacity of signal buffer
  // instead of ignoring new signals when at capacity.
  if (signals_in_buf == signal_buf_cap) {
    return;
  }

  int write_idx = (signal_buf_next_read_idx + signals_in_buf) % signal_buf_cap;
  signal_buf[write_idx] = signum;
  signals_in_buf += 1;

#ifdef _WIN32
  //re-instate signal handler
  signal(signum, _collect_signal);
#endif
}

void _collect_signal(int signum) {
  if (_lock()) {
    _collect_signal_core(signum);
    _unlock();
  }
}

#ifndef _WIN32
inline struct sigaction _simple_handler(void (*handler)(int)) {
  struct sigaction new_action;

  new_action.sa_handler = handler;
  sigemptyset (&new_action.sa_mask);
  new_action.sa_flags = 0;

  return new_action;
}
#endif

int ignore_signal(int signum) {
#ifdef _WIN32
  return signal(signum, SIG_IGN) == SIG_ERR ? -1 : 0;
#else
  struct sigaction handler = _simple_handler(SIG_IGN);
  return sigaction(signum, &handler, NULL);
#endif
}

int default_signal(int signum) {
#ifdef _WIN32
  return signal(signum, SIG_DFL) == SIG_ERR ? -1 : 0;
#else
  struct sigaction handler = _simple_handler(SIG_DFL);
  return sigaction(signum, &handler, NULL);
#endif
}

int collect_signal(int signum) {
#ifdef _WIN32
  return signal(signum, _collect_signal) == SIG_ERR ? -1 : 0;
#else
  struct sigaction handler = _simple_handler(_collect_signal);
  return sigaction(signum, &handler, NULL);
#endif
}

int handle_next_collected_signal() {
  if (_lock()) {
    if (signals_in_buf == 0) {
      _unlock();
      return -1;
    }
    int next = signal_buf[signal_buf_next_read_idx];
    signal_buf_next_read_idx = (signal_buf_next_read_idx + 1) % signal_buf_cap;
    signals_in_buf -= 1;
    _unlock();
    return next;
  }
  return -1;
}

int raise_signal(int signum) {
  return raise(signum);
}

int send_signal(int pid, int signum) {
#ifdef _WIN32
  return raise_signal(signum);
#else
  return kill(pid, signum);
#endif
}

int sighup() {
#ifdef _WIN32
  return -1;
#else
  return SIGHUP;
#endif
}

int sigint() {
  return SIGINT;
}

int sigabrt() {
  return SIGABRT;
}

int sigquit() {
#ifdef _WIN32
  return -1;
#else
  return SIGQUIT;
#endif
}

int sigill() {
  return SIGILL;
}

int sigsegv() {
  return SIGSEGV;
}

int sigtrap() {
#ifdef _WIN32
  return -1;
#else
  return SIGTRAP;
#endif
}

int sigfpe() {
  return SIGFPE;
}

int sigusr1() {
#ifdef _WIN32
  return -1;
#else
  return SIGUSR1;
#endif
}

int sigusr2() {
#ifdef _WIN32
  return -1;
#else
  return SIGUSR2;
#endif
}

