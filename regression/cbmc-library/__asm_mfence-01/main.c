#include <assert.h>
#include <x86_assembler.h>

int main()
{
  __asm_mfence();
  assert(0);
  return 0;
}
