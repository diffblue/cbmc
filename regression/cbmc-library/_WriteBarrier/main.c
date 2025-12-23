#include <assert.h>
#include <intrin.h>

int main()
{
  _WriteBarrier();
  assert(0);
  return 0;
}
