#include <assert.h>
#include <intrin.h>

int main()
{
  _ReadBarrier();
  assert(0);
  return 0;
}
