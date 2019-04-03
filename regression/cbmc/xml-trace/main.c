#include <assert.h>
#include <stdint.h>

union myunion {
  int64_t i;
  double d;
};

void test(union myunion u)
{
  u.i += 1;
  double d = u.d;
  assert(d != 5);
}
