#include <stddef.h>

int main()
{
  // make sure they are NULL objects
  void *p=0, *q=0;
  // with the object:offset encoding we need to make sure the address arithmetic
  // below will only touch the offset part
  __CPROVER_assume(sizeof(unsigned char)<sizeof(void*));
  unsigned char o1, o2;
  // there is ample undefined behaviour here, but the goal of this test solely
  // is exercising CBMC's pointer subtraction encoding
  p+=o1;
  q+=o2;

  ptrdiff_t d=p-q;
  __CPROVER_assert(p-d==q, "");
  return 0;
}
