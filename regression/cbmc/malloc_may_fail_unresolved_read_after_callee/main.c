#include <stdlib.h>

// dup returns early when malloc fails; otherwise it copies 16 bytes.
char *dup(const char *s)
{
  char *p = (char *)malloc(16);
  if(p == 0)
    return 0;
  for(size_t i = 0; i < 16; ++i)
    p[i] = s[i];
  return p;
}

int main()
{
  char *q = dup("bad locale name");
  if(q == 0)
    return 0;
  // only reached when malloc succeeded, so the bytes are the copied ones
  size_t m = 0;
  while(q[m] != 0)
    ++m;
  __CPROVER_assert(m == 15, "length of the copy");
  __CPROVER_assert(0, "WRONG (must FAIL)");
  return 0;
}
