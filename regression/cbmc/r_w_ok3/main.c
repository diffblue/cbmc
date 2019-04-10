#include <assert.h>

int main()
{
  const char *str = "foobar";
  assert(!__CPROVER_w_ok(str, 6));
  assert(__CPROVER_r_ok(str, 6));
}
