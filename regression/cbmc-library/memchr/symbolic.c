#include <assert.h>
#include <string.h>

int main()
{
  char buf[4];
  int c;
  unsigned n;
  __CPROVER_assume(n <= 4);
  char *p = memchr(buf, c, n);
  if(p)
  {
    assert(p >= buf && p < buf + n);
    assert(*(unsigned char *)p == (unsigned char)c);
    for(char *q = buf; q < p; ++q)
      assert((unsigned char)*q != (unsigned char)c);
  }
  else
  {
    for(unsigned i = 0; i < n; ++i)
      assert((unsigned char)buf[i] != (unsigned char)c);
  }
  return 0;
}
