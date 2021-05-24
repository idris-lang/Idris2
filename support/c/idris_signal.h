#ifndef __IDRIS_SIGNAL_H
#define __IDRIS_SIGNAL_H

#include <signal.h>

int ignore_signal(int signum);
int default_signal(int signum);

// Add another signal that should be collected. All collected signals
// should be handled at the earliest convenience by calling
// get_next_pending_signal().
int collect_signal(int signum);

// when collecting signals you can get the next one that has been
// collected but not yet handled with this function.
// Returns -1 to indicate no pending signals.
int handle_next_collected_signal();

// Send a signal to another process.
int send_signal(pid_t pid, int signum);

// available signals in a cross-platform compatible way;
// omits SIGKILL and SIGSTOP because those signals cannot
// be handled in a custom way.
int sigint();
int sigill();
int sigsegv();
int sigfpe();

// Following unavailable in Windows and so mostly defined as -1 in
// this implementation so that they can be unconditionally
// defined in Idris.
// NOTABLE EXCEPTION: SIGQUIT is given a novel code so that it can
// be sent/received to/from Idris programs even under Windows.
int sighup();
int sigquit();
int sigtrap();
int sigusr1();
int sigusr2();

#endif
