#include <assert.h>
#include <x86_assembler.h>

int main()
{
  __asm_sfence();
  assert(0);
  return 0;
}
