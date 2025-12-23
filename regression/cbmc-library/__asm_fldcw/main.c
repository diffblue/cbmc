#include <assert.h>
#include <x86_assembler.h>

int main()
{
  __asm_fldcw();
  assert(0);
  return 0;
}
