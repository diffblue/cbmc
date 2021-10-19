#include <stdbool.h>

bool fail()
{
  __CPROVER_assert(false, "fail function");
  return true;
}

void main()
{
  // clang-format off
  // clang-format would rewrite the "==>" as "== >"
  __CPROVER_assert(false ==> fail(), "fail function");
  // clang-format on
}
