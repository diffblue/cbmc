#include <stdlib.h>
int main()
{
  size_t array_size;
  int a[array_size];

  unsigned int index;
  a[index] = 1;

  assert(a[index] == 1);
  return 0;
}
