#include <assert.h>
#include <intrin.h>

int main()
{
  _mm_mfence();
  assert(0);
  return 0;
}
