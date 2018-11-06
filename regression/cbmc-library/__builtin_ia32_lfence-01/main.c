#include <assert.h>
#include <gcc.h>

int main()
{
  __builtin_ia32_lfence();
  assert(0);
  return 0;
}
