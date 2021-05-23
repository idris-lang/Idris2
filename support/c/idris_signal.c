#include "idris_signal.h"

#include <stdlib.h>
#include <stdio.h>
#include <signal.h>

// TODO: offer Windows support.

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

inline struct sigaction _simple_handler(void (*handler)(int)) {
  struct sigaction new_action;

  new_action.sa_handler = handler;
  sigemptyset (&new_action.sa_mask);
  new_action.sa_flags = 0;

  return new_action;
}

int ignore_signal(int signum) {
  struct sigaction handler = _simple_handler(SIG_IGN);
  return sigaction(signum, &handler, NULL);
}

int default_signal(int signum) {
  struct sigaction handler = _simple_handler(SIG_DFL);
  return sigaction(signum, &handler, NULL);
}

int collect_signal(int signum) {
  struct sigaction handler = _simple_handler(_collect_signal);
  return sigaction(signum, &handler, NULL);
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

int sighup() {
  return SIGHUP;
}

int sigint() {
  return SIGINT;
}

int sigquit() {
  return SIGQUIT;
}

int sigill() {
  return SIGILL;
}

int sigsegv() {
  return SIGSEGV;
}

int sigtrap() {
  return SIGTRAP;
}

int sigfpe() {
  return SIGFPE;
}

int sigusr1() {
  return SIGUSR1;
}

int sigusr2() {
  return SIGUSR2;
}

