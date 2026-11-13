#include <assert.h>

struct str
{
  int x;
  int y;
  int z;
};

int main (void)
{
  int q = __VERIFIER_nondet_int();
  struct str s;

  s.x = q;
  s.y = s.x;
  s.z = s.y;

  assert(q == s.z);

  return 1;
}
