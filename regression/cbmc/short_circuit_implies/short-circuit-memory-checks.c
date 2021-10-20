#include <assert.h>
#include <stdbool.h>
#include <stdlib.h>

int main()
{
  int *c = NULL;

  // clang-format off
  // clang-format would rewrite the "==>" as "== >"
  assert(false ==> *c == 0);
  assert(true ==> *c == 0);
  // clang-format on
}
