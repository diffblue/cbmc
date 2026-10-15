#include <assert.h>

int main()
{
  int unknown;
  int a = 10;
  int b = 10;
  int *p = &a;

  if(unknown)
  {
    b = 15;
    *p = 15;
  }

  assert(*p == b);

  // *p is in [10, 15], so this assertion is provably false (FAILURE).  If a
  // regression let the write-through of *p silently go to top, *p would be
  // unconstrained and this would become UNKNOWN instead, so the probe guards
  // against losing the written-through value.
  assert(*p == 5);
}
