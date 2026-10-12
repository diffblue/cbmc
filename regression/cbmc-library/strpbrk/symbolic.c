#include <assert.h>
#include <string.h>

int main()
{
  // nondeterministic contents, so that the loops are explored symbolically
  char s1[4], s2[3];
  s1[3] = 0;
  s2[2] = 0;
  char *p = strpbrk(s1, s2);
  if(p)
  {
    assert(p >= s1 && p < s1 + 3 && *p != 0 && strchr(s2, *p));
    // C23 7.26.5.5: the first such character
    for(char *q = s1; q < p; q++)
      assert(!strchr(s2, *q));
  }
  else
  {
    for(int i = 0; i < 3 && s1[i]; i++)
      assert(!strchr(s2, s1[i]));
  }
  return 0;
}
