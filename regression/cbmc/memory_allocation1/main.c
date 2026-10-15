#include <assert.h>

int main()
{
  int *p=0x10;

#ifndef CMDLINE
  __CPROVER_allocated_memory(0x10, sizeof(int));
#endif
  *p=42;
  assert(*p==42);
  *(p+1)=42;
  assert(*(p+1)==42);

  return 0;
}
