#include <assert.h>
#include <stdlib.h>

int main()
{
  char *p = calloc(-1, -1);
  if(p)
    assert(p[0] == 0);
}
