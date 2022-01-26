#pragma once

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

// Raise a signal to the current process.
int raise_signal(int signum);

// Send a signal to another process.
// IMPORTANT: On Windows you cannot send to other processes
// so this is implemented as `raise_signal()` which sends the signal
// to the calling process.
int send_signal(int pid, int signum);

// available signals in a cross-platform compatible way;
// omits SIGKILL and SIGSTOP because those signals cannot
// be handled in a custom way.
int sigint();
int sigill();
int sigsegv();
int sigfpe();
int sigabrt();

// Following unavailable in Windows and defined as -1 in
// this implementation so that they can be unconditionally
// defined in Idris.
int sighup();
int sigquit();
int sigtrap();
int sigusr1();
int sigusr2();
