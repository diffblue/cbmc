#include <assert.h>
#include <stdlib.h>

int main()
{
  int **s = malloc(sizeof(int *));
  for(int i = 0; i < sizeof(int *); ++i)
  {
    // A correct program would use (char *)s, but updating the pointer allows us
    // to reproduce a bug in CBMC (missing support for typecasts from bv_typet
    // to pointers).
    *((char *)&s + i) = 0;
  }
  assert(s[0] == 0);
}
