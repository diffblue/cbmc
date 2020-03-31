#include <stdlib.h>

void main()
{
  char *p = (char *)10;
  p -= 1;
  p += 1;
  p += -1; // spurious pointer overflow report
  p -= -1; // spurious pointer overflow report
}
