#include <assert.h>
#include <stdlib.h>

int main()
{
  int i;
  char *a;
  char *b;
  char *c;
  a = (char *)malloc(1);
  b = (char *)malloc(1);
  c = (char *)malloc(1);
  for(i = 0; i < 5; ++i)
  {
    *a = 0;
    *b = 0;
    *c = 0;
  }
  assert(*c + *b + *c == 1);
}
