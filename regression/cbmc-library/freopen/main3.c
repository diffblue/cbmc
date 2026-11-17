#include <stdio.h>

int main(void)
{
  FILE *f = fopen("/dev/null", "r");
  if(!f)
    return 0;
  // C11 7.21.5.4p4: the stream is closed even when opening fails
  FILE *g = freopen("/nonexistent-dir/x", "r", f);
  if(!g)
    fclose(f); // must fail: f has already been closed
  return 0;
}
