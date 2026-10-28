#include <assert.h>
#include <stdio.h>

int main(void)
{
  FILE *f = fopen("/dev/null", "r");
  if(!f)
    return 0;
  // C11 7.21.5.4p5: freopen returns a null pointer if the open fails
  FILE *g = freopen("/nonexistent-dir/x", "r", f);
  assert(g != NULL); // must FAIL: freopen can return NULL
  return 0;
}
