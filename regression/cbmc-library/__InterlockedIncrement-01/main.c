#include <assert.h>
#include <intrin.h>

int main()
{
  __InterlockedIncrement();
  assert(0);
  return 0;
}
