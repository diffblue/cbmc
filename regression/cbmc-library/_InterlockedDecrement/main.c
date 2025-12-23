#include <assert.h>
#include <intrin.h>

int main()
{
  _InterlockedDecrement();
  assert(0);
  return 0;
}
