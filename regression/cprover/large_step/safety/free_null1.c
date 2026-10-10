#include <stdlib.h>

int main()
{
  free(0);             // safe
  free((char *)0 + 1); // unsafe
}
