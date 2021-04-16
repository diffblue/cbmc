#include <stdlib.h>
#include <string.h>

void main()
{
  char *data = nondet() ? NULL : malloc(8);
  memset(data, 0, 8);
  memset(data, 0, 8);
}
