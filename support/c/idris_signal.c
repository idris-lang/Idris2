#include "idris_signal.h"

#include <assert.h>
#include <errno.h>
#include <limits.h>
#include <signal.h>
#include <stdatomic.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "idris_util.h"

static_assert(ATOMIC_LONG_LOCK_FREE == 2,
              "when not lock free, atomic functions are not async-signal-safe");

#define N_SIGNALS 32
static atomic_uint_fast32_t signals;

void _collect_signal(int signum) {
  IDRIS2_VERIFY(signum >= 0 && signum < N_SIGNALS,
                "signal number out of range: %d", signum);

  atomic_fetch_or(&signals, (uint32_t)1 << signum);

#ifdef _WIN32
  // re-instate signal handler
  IDRIS2_VERIFY(signal(signum, _collect_signal) != SIG_ERR, "signal failed: %s",
                strerror(errno));
#endif
}

#ifndef _WIN32
static inline struct sigaction _simple_handler(void (*handler)(int)) {
  struct sigaction new_action;

  new_action.sa_handler = handler;
  sigemptyset(&new_action.sa_mask);
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
  uint32_t signals_snapshot = atomic_load(&signals);
  if (signals_snapshot == 0) {
    return -1;
  }
  for (uint32_t signum = 0; signum != N_SIGNALS; ++signum) {
    uint32_t mask = (uint32_t)1 << signum;
    if ((signals_snapshot & mask) != 0) {
      atomic_fetch_and(&signals, ~mask);
      return signum;
    }
  }
  abort();
}

int raise_signal(int signum) { return raise(signum); }

int send_signal(int pid, int signum) {
#ifdef _WIN32
  // TODO: ignores pid
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

int sigint() { return SIGINT; }

int sigabrt() { return SIGABRT; }

int sigquit() {
#ifdef _WIN32
  return -1;
#else
  return SIGQUIT;
#endif
}

int sigill() { return SIGILL; }

int sigsegv() { return SIGSEGV; }

int sigtrap() {
#ifdef _WIN32
  return -1;
#else
  return SIGTRAP;
#endif
}

int sigfpe() { return SIGFPE; }

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
