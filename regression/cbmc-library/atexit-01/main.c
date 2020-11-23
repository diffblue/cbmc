#include <assert.h>
#include <stdlib.h>

void cleanup()
{
  assert(0);
}

int main()
{
  atexit(cleanup);
}
