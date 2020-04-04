#include <assert.h>
#include <stdlib.h>

int main()
{
  char *x = malloc(sizeof(char) * 10);
  x[8] = '\0';
  assert(strlen(x) == 8);
}
