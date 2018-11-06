#include <assert.h>
#include <intrin.h>

int main()
{
  _ReadWriteBarrier();
  assert(0);
  return 0;
}
