#include <assert.h>
#include <intrin.h>

int main()
{
  _mm_lfence();
  assert(0);
  return 0;
}
