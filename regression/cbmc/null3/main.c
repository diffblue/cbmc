#include <assert.h>
#include <stdlib.h>

struct S
{
  int a;
  int b;
};

int main()
{
  struct S s;
  int* b_ptr=&(s.b);

  if((size_t)((struct S*)0)!=0)
    return 1;

  struct S* s_ptr=(struct S*)((char*)b_ptr - ((size_t) &((struct S*)0)->b));
  assert(s_ptr==&s);

  return 0;
}
