#include <stdio.h>

int main(void)
{
  FILE *f = fopen("/dev/null", "r");
  if(!f)
    return 0;
  FILE *g = freopen("/dev/null", "r", f);
  if(!g)
    return 0; // freopen has closed f
  fclose(g);
  return 0;
}
