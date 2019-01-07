#include <stdlib.h>

int main()
{
  int *p = malloc(2 * sizeof(int)), *p2;
  size_t other1, other2;

  p2 = p + other1;
  p2 = p + other2 + other1;
  p2 = other1 + other2 + p;
  p2 = p - other1;
  p2 = p - other2 - other1;

  p2 = p + sizeof(int);
  p2 = p + sizeof(int) + sizeof(int);

  return 0;
}
