#include "declarations.h"

void main(void)
{
  // INITIALIZE
  uint16_t a = 1;
  st old_s = {
    .a = 1, .b = {0, 1, 2, 3, 4}, .c = 2, .d = &a, .u.b = {0, 1, 2, 3, 4}};
  st s = old_s;

  // Interpret as bytes
  char *c = (char *)&s;
  char *old_c = (char *)&old_s;

  // HAVOC SOME BYTE LEVEL SLICE
  __CPROVER_havoc_slice(c + 7, 11);

  // POSTCONDITION
  // TODO
  __CPROVER_assert(c[0] == old_c[0], "expecting SUCCESS");
  __CPROVER_assert(c[1] == old_c[1], "expecting SUCCESS");
  __CPROVER_assert(c[2] == old_c[2], "expecting SUCCESS");
  __CPROVER_assert(c[3] == old_c[3], "expecting SUCCESS");
  __CPROVER_assert(c[4] == old_c[4], "expecting SUCCESS");
  __CPROVER_assert(c[5] == old_c[5], "expecting SUCCESS");
  __CPROVER_assert(c[6] == old_c[6], "expecting SUCCESS");
  __CPROVER_assert(c[7] == old_c[7], "expecting FAILURE");
  __CPROVER_assert(c[8] == old_c[8], "expecting FAILURE");
  __CPROVER_assert(c[9] == old_c[9], "expecting FAILURE");
  __CPROVER_assert(c[10] == old_c[10], "expecting FAILURE");
  __CPROVER_assert(c[11] == old_c[11], "expecting FAILURE");
  __CPROVER_assert(c[12] == old_c[12], "expecting FAILURE");
  __CPROVER_assert(c[13] == old_c[13], "expecting FAILURE");
  __CPROVER_assert(c[14] == old_c[14], "expecting FAILURE");
  __CPROVER_assert(c[15] == old_c[15], "expecting FAILURE");
  __CPROVER_assert(c[16] == old_c[16], "expecting FAILURE");
  __CPROVER_assert(c[17] == old_c[17], "expecting FAILURE");
  __CPROVER_assert(c[18] == old_c[18], "expecting SUCCESS");
  __CPROVER_assert(c[19] == old_c[20], "expecting SUCCESS");
  return;
}
