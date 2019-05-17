#include <assert.h>
#include <stdint.h>
#include <stdlib.h>

int main()
{
  char *p = calloc(-1, -1);
  if(p)
    assert(p[0] == 0);

  p = calloc(SIZE_MAX, 1);
  if(p)
    assert(p[0] == 0);

  size_t size;
  size_t num;
  p = calloc(size, num);
  if(p && size > 0 && num > 0)
    assert(p[0] == 0);
}
