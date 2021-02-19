#include <stddef.h>

int main()
{
  int array[1 << (sizeof(unsigned char) * 8)];

  void *p = array, *q = array;
  // with the object:offset encoding we need to make sure the address arithmetic
  // below will only touch the offset part
  __CPROVER_assume(sizeof(unsigned char)<sizeof(void*));
  unsigned char o1, o2;

  p+=o1;
  q+=o2;

  ptrdiff_t d=p-q;
  __CPROVER_assert(p-d==q, "");
  return 0;
}
