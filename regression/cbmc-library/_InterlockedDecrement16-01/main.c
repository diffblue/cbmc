#include <assert.h>
#include <intrin.h>

int main()
{
  _InterlockedDecrement16();
  assert(0);
  return 0;
}
