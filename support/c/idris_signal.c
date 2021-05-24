#include "idris_signal.h"

#include <stdlib.h>
#include <stdio.h>
#include <signal.h>

#ifdef _WIN32
#include <windows.h>
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

void _collect_signal(int signum) {
  _init_buf();
  
  // TODO: mutex lock around rest of function

  // FIXME: allow for adjusting capacity of signal buffer
  // instead of ignoring new signals when at capacity.
  if (signals_in_buf == signal_buf_cap) {
    return;
  }

  int write_idx = (signal_buf_next_read_idx + signals_in_buf) % signal_buf_cap;
  signal_buf[write_idx] = signum;
  signals_in_buf += 1;
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
  // TODO: mutex lock
  if (signals_in_buf == 0) {
    return -1;
  }
  int next = signal_buf[signal_buf_next_read_idx];
  signal_buf_next_read_idx = (signal_buf_next_read_idx + 1) % signal_buf_cap;
  signals_in_buf -= 1;
  return next;
}

int raise_signal(int signum) {
  return raise(signum);
}

int send_signal(pid_t pid, int signum) {
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

