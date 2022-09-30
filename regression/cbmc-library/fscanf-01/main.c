#include <assert.h>
#include <stdio.h>

int main()
{
  FILE *f = fopen("main.c", "r");
  if(f == NULL)
    return 1;
  char dest[10];
  int result = fscanf(f, "%s", dest);
  assert(result == 1);
  return 0;
}
