#include "declarations.h"

void main(void)
{
  // INITIALIZE
  uint16_t a = 1;
  st old_s = {
    .a = 1, .b = {0, 1, 2, 3, 4}, .c = 2, .d = &a, .u.b = {0, 1, 2, 3, 4}};
  st s = old_s;

  // HAVOC FOURTH MEMBER (PTR)
  __CPROVER_havoc_slice(&s.d, sizeof(s.d));

  // POSTCONDITIONS
  __CPROVER_assert(s.a == old_s.a, "expecting SUCCESS");
  __CPROVER_assert(s.b[0] == old_s.b[0], "expecting SUCCESS");
  __CPROVER_assert(s.b[1] == old_s.b[1], "expecting SUCCESS");
  __CPROVER_assert(s.b[2] == old_s.b[2], "expecting SUCCESS");
  __CPROVER_assert(s.b[3] == old_s.b[3], "expecting SUCCESS");
  __CPROVER_assert(s.b[4] == old_s.b[4], "expecting SUCCESS");
  __CPROVER_assert(s.c == old_s.c, "expecting SUCCESS");
  __CPROVER_assert(s.d == old_s.d, "expecting FAILURE");
  __CPROVER_assert(s.u.a == old_s.u.a, "expecting SUCCESS");
  __CPROVER_assert(s.u.b[0] == old_s.u.b[0], "expecting SUCCESS");
  __CPROVER_assert(s.u.b[1] == old_s.u.b[1], "expecting SUCCESS");
  __CPROVER_assert(s.u.b[2] == old_s.u.b[2], "expecting SUCCESS");
  __CPROVER_assert(s.u.b[3] == old_s.u.b[3], "expecting SUCCESS");
  __CPROVER_assert(s.u.b[4] == old_s.u.b[4], "expecting SUCCESS");
  __CPROVER_assert(s.u.c == old_s.u.c, "expecting SUCCESS");
  __CPROVER_assert(s.u.d == old_s.u.d, "expecting SUCCESS");
}
