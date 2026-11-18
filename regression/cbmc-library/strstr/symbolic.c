#include <assert.h>
#include <string.h>

int main()
{
  // nondeterministic contents, so that the loops are explored symbolically
  char h[4], n[3];
  h[3] = 0;
  n[2] = 0;
  char *r = strstr(h, n);
  if(r)
  {
    assert(r >= h && r <= h + 3);
    assert(strncmp(r, n, strlen(n)) == 0);
    // C23 7.26.5.8: the first occurrence
    for(char *q = h; q < r; q++)
      assert(strncmp(q, n, strlen(n)) != 0);
  }
  else
  {
    for(int i = 0; i <= (int)strlen(h); i++)
      assert(strncmp(h + i, n, strlen(n)) != 0);
  }
  return 0;
}
