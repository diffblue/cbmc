// A single struct with more than 1000 pointers: without an explicit
// --max-dynamic-object-instances, every one of them may point to an object.
#include <assert.h>
struct S
{
  int *a[1001];
};
void f(struct S s)
{
  if(s.a[1000] != 0)
    assert(0);
}
