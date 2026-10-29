#include <stdlib.h>

void main()
{
#ifndef CMDLINE
  __CPROVER_allocated_memory(9, sizeof(char));
#endif
  char *p = (char *)10;
  p -= 1;
  p += 1;
  p += -1; // previously: spurious pointer overflow report
  p -= -1; // previously: spurious pointer overflow report
}
