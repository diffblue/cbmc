#include <assert.h>
#include <intrin.h>

int main()
{
  _InterlockedIncrement16();
  assert(0);
  return 0;
}
