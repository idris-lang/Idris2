#ifndef __IDRIS_SIGNAL_H
#define __IDRIS_SIGNAL_H

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

// available signals in a cross-platform compatible way;
// omits SIGKILL and SIGSTOP because those signals cannot
// be handled in a custom way.
int sighup();
int sigint();
int sigquit();
int sigill();
int sigsegv();
int sigtrap();
int sigfpe();
int sigusr1();
int sigusr2();

#endif
