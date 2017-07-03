#ifndef _WIN32

#include <signal.h>
#include <stdlib.h>

void sig_block(int sig)
{
  sigset_t ss;
  sigemptyset(&ss);
  sigaddset(&ss, sig);
  sigprocmask(SIG_BLOCK, &ss, NULL);
}

int main() {
  sig_block(0);
  return 0;
}
#else
int main()
{
  return 0;
}
#endif
