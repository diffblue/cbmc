#include <assert.h>
#include <stdio.h>

int main(void)
{
  FILE *f = fopen("/dev/null", "r");
  if(!f)
    return 0;
  // C11 7.21.5.4p3: a null filename changes the mode of the stream
  FILE *g = freopen(NULL, "rb", f);
  if(g)
  {
    assert(g == f);
    fclose(g);
  }
  return 0;
}
