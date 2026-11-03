#ifndef _WIN32

#  include <arpa/inet.h>

#  include <assert.h>

int main(void)
{
  struct in_addr a;
  a.s_addr = 0;

  int r = inet_aton("1.2.3.4", &a);

  // On success, the model must have written *pin, so a.s_addr is
  // nondeterministic and not necessarily 0.  The old model never
  // wrote *pin, so a.s_addr stayed 0 and this assertion was proved
  // (wrongly reported as VERIFICATION SUCCESSFUL).
  if(r)
    assert(a.s_addr == 0); // must FAIL: s_addr is nondeterministic

  return 0;
}

#else

int main(void)
{
  return 0;
}

#endif
