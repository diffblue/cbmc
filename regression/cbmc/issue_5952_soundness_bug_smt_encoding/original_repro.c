#include <assert.h>
#include <stdbool.h>
#include <stdlib.h>

bool validate(const char *data, unsigned allocated)
{
  // clang-format off
  bool check_1 = (data == NULL ==> allocated == 0);
  bool check_2 = (allocated != 0 ==> __CPROVER_r_ok(data, allocated));
  // clang-format on
  return check_1 && check_2;
}

void main()
{
  char *data;
  unsigned allocated;

  data = (allocated == 0) ? NULL : malloc(allocated);

  __CPROVER_assume(validate(data, allocated));

  assert(validate(data, allocated));
}
