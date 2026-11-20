#include <assert.h>
#include <stdio.h>

int main()
{
  // a nondeterministic value: the model does not need --unwind
  unsigned x;
  char b[80];
  int r = snprintf(b, sizeof b, "%u", x);
  assert(r >= 1 && r <= 10 && b[r] == 0);
  return 0;
}
