#include <assert.h>
#include <gcc.h>

int main()
{
  __builtin_ia32_mfence();
  assert(0);
  return 0;
}
