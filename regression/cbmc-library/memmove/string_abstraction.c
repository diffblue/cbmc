#include <assert.h>
#include <string.h>

int main()
{
  char src[4] = "x";
  // not zero-terminated before the copies
  char dst[4] = {'y', 'y', 'y', 'y'};
  memmove(dst, src, 2);
  assert(strlen(dst) == 1);
  char dst_chk[4] = {'y', 'y', 'y', 'y'};
  __builtin___memmove_chk(dst_chk, src, 2, ~(__CPROVER_size_t)0);
  assert(strlen(dst_chk) == 1);
  return 0;
}
